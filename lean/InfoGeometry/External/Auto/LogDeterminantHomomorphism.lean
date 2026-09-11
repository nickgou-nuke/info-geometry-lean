import Init
import InfoGeometry.Algebra.FiniteSpinAlgebra

class LogTensorProduct (α : Type) where
  tensor : α → α → α
  dim : α → Int

infix:70 " ⊗ " => LogTensorProduct.tensor

class LogDetHomomorphism (Operator : Type) [LogTensorProduct Operator] [Mul Operator] where
  logDet : Operator → Int
  jacobian : Operator → Operator
  additivity : ∀ (A B : Operator), logDet (A * B) = logDet A + logDet B
  tensor_prod : ∀ (A B : Operator), logDet (A ⊗ B) = (LogTensorProduct.dim B) * logDet A + (LogTensorProduct.dim A) * logDet B
  log_det_jacobian : ∀ (A B : Operator), logDet (jacobian (A ⊗ B)) = (LogTensorProduct.dim B) * logDet (jacobian A) + (LogTensorProduct.dim A) * logDet (jacobian B)

theorem neg_log_det_jacobian_tensor_additivity
  {Operator : Type} [LogTensorProduct Operator] [Mul Operator] [LogDetHomomorphism Operator]
  (A B : Operator) :
  - LogDetHomomorphism.logDet (LogDetHomomorphism.jacobian (A ⊗ B)) =
  - ((LogTensorProduct.dim B) * LogDetHomomorphism.logDet (LogDetHomomorphism.jacobian A))
  - ((LogTensorProduct.dim A) * LogDetHomomorphism.logDet (LogDetHomomorphism.jacobian B)) := by
  rw [LogDetHomomorphism.log_det_jacobian A B]
  omega
