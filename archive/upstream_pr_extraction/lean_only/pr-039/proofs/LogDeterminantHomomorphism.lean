import Init

class TensorProduct (α : Type) where
  tensor : α → α → α
  dim : α → Int

infix:70 " ⊗ " => TensorProduct.tensor

class LogDetHomomorphism (Operator : Type) [TensorProduct Operator] [Mul Operator] where
  logDet : Operator → Int
  jacobian : Operator → Operator
  additivity : ∀ (A B : Operator), logDet (A * B) = logDet A + logDet B
  tensor_prod : ∀ (A B : Operator), logDet (A ⊗ B) = (TensorProduct.dim B) * logDet A + (TensorProduct.dim A) * logDet B
  log_det_jacobian : ∀ (A B : Operator), logDet (jacobian (A ⊗ B)) = (TensorProduct.dim B) * logDet (jacobian A) + (TensorProduct.dim A) * logDet (jacobian B)

theorem neg_log_det_jacobian_tensor_additivity
  {Operator : Type} [TensorProduct Operator] [Mul Operator] [LogDetHomomorphism Operator]
  (A B : Operator) :
  - LogDetHomomorphism.logDet (LogDetHomomorphism.jacobian (A ⊗ B)) =
  - ((TensorProduct.dim B) * LogDetHomomorphism.logDet (LogDetHomomorphism.jacobian A))
  - ((TensorProduct.dim A) * LogDetHomomorphism.logDet (LogDetHomomorphism.jacobian B)) := by
  rw [LogDetHomomorphism.log_det_jacobian A B]
  omega
