use aiken/hash.{Blake2b_224, Hash}
use aiken/interval
use aiken/list
use aiken/option
use aiken/time.{PosixTime}
use aiken/transaction.{
  InlineDatum, Input, NoDatum, Output, OutputReference, ScriptContext, Spend,
  Transaction, TransactionId, ValidityRange, find_input,
}
use aiken/transaction/credential.{
  Address, VerificationKey, VerificationKeyCredential,
}
use aiken/transaction/value.{
  AssetName, PolicyId, Value, ada_asset_name, ada_policy_id,
}

type PubKeyHash =
  Hash<Blake2b_224, VerificationKey>

// ---------------------------------------------------------------------

type Loan {
  lender: PubKeyHash,
  value: Int,
  securityCollateral: Int,
}

type LoanDatum {
  borrower: PubKeyHash,
  deadline: PosixTime,
  loanAmount: Int,
  repaymentAmount: Int,
  policy_id: PolicyId,
  asset_name: AssetName,
  loan: Option<Loan>,
}

type LoanRedeemer {
  Lend(Loan)
  CloseLoan
  ClaimCollateral
}

validator {
  fn loan(data: LoanDatum, redeemer: LoanRedeemer, ctx: ScriptContext) -> Bool {
    expect Spend(ownOutputRef) = ctx.purpose
    expect Some(ownInput) = find_input(ctx.transaction.inputs, ownOutputRef)

    let getOwnOutput =
      fn() -> Output {
        expect [ownOutput] = {
          let isOwnOutput =
            fn(o: Output) -> Bool { o.address == ownInput.output.address }
          ctx.transaction.outputs |> list.filter(isOwnOutput)
        }
        ownOutput
      }

    let sufficientLoan =
      fn(loan: Loan) -> Bool {
        when data.loan is {
          None -> data.loanAmount <= loan.value
          Some(loan) -> False
        }
      }

    let correctLoanOutputDatum =
      fn(loan: Loan) -> Bool {
        expect InlineDatum(ownOutputDatumUntyped) = getOwnOutput().datum
        expect ownOutputDatum: LoanDatum = ownOutputDatumUntyped

        data.borrower == ownOutputDatum.borrower && data.deadline == ownOutputDatum.deadline && data.loanAmount == ownOutputDatum.loanAmount && data.repaymentAmount == ownOutputDatum.repaymentAmount && data.policy_id == ownOutputDatum.policy_id && data.asset_name == ownOutputDatum.asset_name && Some(
          loan,
        ) == ownOutputDatum.loan
      }

    let correctLoanOutputValue =
      fn(val: Int) -> Bool {
        getOwnOutput().value == (
          value.from_lovelace(val)
            |> value.add(data.policy_id, data.asset_name, 1)
        )
      }

    let getValueSentToAddress =
      fn(address: PubKeyHash, policy_id: PolicyId, asset_name: AssetName) -> Int {
        let f =
          fn(o: Output, i: Int) -> Int {
            if
            o.address.payment_credential == VerificationKeyCredential(address){
            
              i + value.quantity_of(o.value, policy_id, asset_name)
            } else {
              i
            }
          }
        list.foldr(ctx.transaction.outputs, 0, f)
      }

    let correctBidRefund =
      fn() -> Bool {
        when data.loan is {
          None -> True
          Some(bid) ->
            getValueSentToAddress(bid.lender, ada_policy_id, ada_asset_name) >= bid.value
        }
      }

    let correctLoanSlotRange =
      fn() -> Bool {
        interval.is_entirely_before(
          ctx.transaction.validity_range,
          data.deadline,
        )
      }

    let correctClaimSlotRange =
      fn() -> Bool {
        interval.is_entirely_after(
          ctx.transaction.validity_range,
          data.deadline,
        )
      }

    let borrowerGetsToken =
      fn() -> Bool {
        getValueSentToAddress(data.borrower, data.policy_id, data.asset_name) >= 1
      }

    let lenderGetsToken =
      fn(loan: Loan) -> Bool {
        getValueSentToAddress(loan.lender, data.policy_id, data.asset_name) >= 1
      }

    let lenderGetsRepay =
      fn(loan: Loan) -> Bool {
        getValueSentToAddress(loan.lender, ada_policy_id, ada_asset_name) >= data.repaymentAmount
      }

    let borrowerGetsLoan =
      fn() -> Bool {
        getValueSentToAddress(data.borrower, ada_policy_id, ada_asset_name) >= data.loanAmount
      }

    let correctClose =
      fn() -> Bool {
        when data.loan is {
          None -> borrowerGetsToken()?

          Some(loan) -> borrowerGetsToken()? && lenderGetsRepay(loan)?
        }
      }

    let claimToken =
      fn() -> Bool {
        when data.loan is {
          None -> borrowerGetsToken()?

          Some(loan) -> lenderGetsToken(loan)?
        }
      }

    when redeemer is {
      Lend(loan) ->
        sufficientLoan(loan)? && borrowerGetsLoan()? && correctLoanOutputDatum(
          loan,
        )? && correctLoanOutputValue(loan.securityCollateral)? && correctLoanSlotRange()?
      CloseLoan -> correctClose()? && correctLoanSlotRange()?
      ClaimCollateral -> claimToken()? && correctClaimSlotRange()?
    }
  }
}
