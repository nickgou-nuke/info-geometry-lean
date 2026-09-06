import DAG.Util

namespace DAG


private def boolVecTrue (byteWidth : Nat) : ByteArray :=
  ByteArray.mk (arrayReplicate byteWidth (0xFF : UInt8))

private def boolVecZero (byteWidth : Nat) : ByteArray :=
  ByteArray.mk (arrayReplicate byteWidth (0 : UInt8))

private def boolVecAnd (a b : ByteArray) : ByteArray :=
  Id.run do
    let mut r := ByteArray.empty
    for i in [:a.size] do
      r := r.push (a[i]! &&& b[i]!)
    r

private def boolVecSet (a : ByteArray) (i : Nat) : ByteArray :=
  let bi := i / 8
  let bit : UInt8 := 1 <<< (i % 8).toUInt8
  a.set! bi (a[bi]! ||| bit)

/-- DAG dominators -/

def dominators (preds : Array (Array Nat)) (order : Array Nat) : Array ByteArray := Id.run do
  let m := preds.size
  let byteWidth := (m + 7) / 8
  let mut dom := arrayReplicate m (boolVecTrue byteWidth)

  for u in order do
    let ps := preds[u]!
    let base :=
      match ps[0]? with
      | none => boolVecZero byteWidth
      | some p0 =>
          Id.run do
            let mut acc := dom[p0]!
            for i in [1:ps.size] do
              acc := boolVecAnd acc (dom[ps[i]!]!)
            acc
    dom := dom.set! u (boolVecSet base u)

  dom

end DAG
