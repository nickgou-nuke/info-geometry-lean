theory BrillouinKlein
  imports Main
begin

axiomatization Tx Ty :: "'a::ring_1" where
  Tx_sq: "Tx * Tx = 1" and
  Ty_sq: "Ty * Ty = 1" and
  anti_comm: "Tx * Ty = - (Ty * Tx)"

lemma TxTy_sq: "(Tx * Ty) * (Tx * Ty) = -1"
proof -
  have "(Tx * Ty) * (Tx * Ty) = Tx * (Ty * Tx) * Ty"
    by (simp add: mult.assoc)
  also have "... = Tx * (- (Tx * Ty)) * Ty"
    by (simp add: anti_comm)
  also have "... = - ((Tx * Tx) * (Ty * Ty))"
    by (simp add: mult.assoc)
  also have "... = - (1 * 1)"
    by (simp add: Tx_sq Ty_sq)
  finally show ?thesis
    by simp
qed

end
