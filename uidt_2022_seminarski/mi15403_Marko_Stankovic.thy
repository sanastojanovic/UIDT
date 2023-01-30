theory mi15403_Marko_Stankovic
  imports Main HOL.Real HOL.Rings Complex_Main
(* "HOL-Algebra.Multiplicative" *)
begin

(* A1 problem *)
(* https://www.imo-official.org/problems/IMO2015SL.pdf *)

text \<open>Seminarski
Suppose that a sequence a1, a2, . . . of positive real numbers satisfies
a(k+1) \<ge> (k * a (k) / ((a(k))^2 + (k - 1)), k \<ge> 1 for every positive integer k.
Prove that a1 + a2 + ... + an \<ge> n for every n \<ge> 2.
\<close>

(* Lema (2) u dokazu, nakon koje bi trebalo primeniti AM_GM nejednakost *)
(* a1 + a2 + ... + am \<ge> m / a(m+1)*)

(*
lemma middle_step_lemma:
  fixes theList :: "real list" and n :: "nat" and m :: "nat"
  assumes "n \<ge> 3"
  assumes "m \<in> (set [2 .. n-2])"
  assumes "length theList = n"
  assumes "\<forall> x. x \<in> (set theList) \<longrightarrow> x > 0"
  assumes "k \<in> (set [1 .. n-1])"
  assumes "(theList ! (k+1)) \<ge> (k * (theList ! k)) / ((theList ! k)\<^sup>2 + k - 1)"
  assumes "k / (theList ! (k + 1)) - (k - 1) / (theList ! k) \<le> theList ! k"
  shows "m / (theList ! (m + 1)) \<le> (\<Sum> i \<leftarrow> [1..m]. theList ! i)"

  sorry

*)

lemma AM_GM_inequality:
  fixes x y :: real
  assumes "x > 0" "y > 0" 
  shows "x + y \<ge> 2 * sqrt (x*y)"
  using assms
  by (metis less_eq_real_def mult.assoc real_sqrt_mult real_sqrt_pow2 sum_squares_bound)

lemma sum_fraction_with_real:
  fixes a b :: real and k :: nat
  assumes "a > 0"
  assumes "b > 0"
  shows "a + k / b = (a * b + k) / b"
  by (metis add.commute assms(2) divide_add_eq_iff less_numeral_extra(3))


(*
lemma Transformed:
  fixes sequence :: "real list" and n :: "nat"
  assumes "length sequence = m"
  assumes "\<forall> x. x \<in> (set sequence) \<longrightarrow> x > 0"
  assumes "k \<in> (set [1 .. m-1])"
  assumes "sequence ! (k+1) \<ge> (k * (sequence ! k)) / ((sequence ! k)\<^sup>2 + k - 1)"
  shows "sum_list sequence \<ge> (m / sequence ! (m+1))"
proof-
  have "(sequence ! (k+1)) / k \<ge> (sequence ! k) / ((sequence ! k)\<^sup>2 + k - 1)"
    
qed
*)



(* Ako vazi a \<ge> b, kada obe strane pomnozimo pozitivnim k vazice i ka \<ge> kb *)
lemma ineq_mult_both_sides [simp]:
  fixes a b k :: real
  assumes "k \<ge> 0"
  assumes "a \<ge> b"
  shows "k * a \<ge> k * b"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "k * a < k * b" by (simp add: not_le)
  then have "a < b" by (simp add: assms(1) mult_less_cancel_left)
  from this assms(2) show False by auto
qed


theorem Algebra_A1_IMO2015:
  fixes sequence :: "real list" and n :: "nat"
  assumes "length sequence = n"
  assumes "\<forall> x. x \<in> (set sequence) \<longrightarrow> x > 0"
  assumes "k \<in> (set [1 .. n-1])"
  assumes "sequence ! (k+1) \<ge> (k * (sequence ! k)) / ((sequence ! k)\<^sup>2 + k - 1)"
  assumes "n \<ge> 2"
  shows "sum_list sequence \<ge> n"
proof-
  have "(sequence ! (k+1)) * (1/k) \<ge> (k * (sequence ! k)) / ((sequence ! k)\<^sup>2 + k - 1) * (1/k)" (* Mnozimo obe stranse sa 1/k *)
    sorry
    (* by (metis assms(4) bot_nat_0.extremum ineq_mult_both_sides mult.commute numeral_One of_nat_0 of_nat_le_iff zero_le_divide_iff zero_le_numeral) *)
  then have "(sequence ! (k+1)) * (1/k) \<ge> (sequence ! k) / ((sequence ! k)\<^sup>2 + k - 1)" (* Pojednostavimo desnu stranu nejednakosti *) 
    sorry
  then have "k * (1 / sequence ! (k+1)) \<le> ((sequence ! k)\<^sup>2 + k - 1) / (sequence ! k)" (* Transofrmisemo nejednakost *)
    sorry
  then have "k * (1 / sequence ! (k+1)) \<le> (sequence ! k) + (k - 1) / (sequence ! k)" 
    (* Desnu stranu nejednakosti predstavljamo uz sum_fraction_with_real *)
    sorry 
  then have "sequence ! k \<ge> (k / sequence ! (k + 1)) - ((k-1)/ sequence ! k)" 
    (* Ostavljamo k-ti clan niza sa jedne strane nejednakosti, a ostatak prebacujemo na drugu stranu *)
    sorry
  then have "sum_list sequence \<ge> n / sequence ! (n + 1)" (* Tvrdjenje (2) u dokazu *)
    sorry

qed


(* Drugi pristup, pretpostavimo da je pocetna nejednakost transformisana do nejedanokosti pre
"Summing up" linije *)
(*
theorem Algebra_A1_IMO2015_Simpler:
  fixes sequence :: "real list" and m :: "nat"
  assumes "length sequence = m"
  assumes "\<forall> x. x \<in> (set sequence) \<longrightarrow> x > 0"
  assumes "k \<in> (set [1 .. m])"
  assumes "sequence ! k \<ge> (k / sequence ! (k + 1)) - (k - 1) / sequence ! k"
  assumes "n \<ge> 2"
  shows "sum_list sequence \<ge> n / sequence ! (n + 1)"
proof (induction n)
  case 0
  show ?case
  by (metis assms(2) less_eq_real_def of_nat_0_eq_iff ordered_comm_monoid_add_class.sum_list_nonneg)
next
  case (Suc n)
  show (?case)
*)

theorem Algebra_A1_IMO2015_Final:
  fixes sequence :: "real list" and m :: "nat"
  assumes "length sequence = m"
  assumes "\<forall> x. x \<in> (set sequence) \<longrightarrow> x > 0"
  assumes "m \<ge> 2"
  assumes "sequence ! (m+1) > 1"
  assumes "sum_list sequence \<ge> (m / sequence ! (m+1))"
  shows "sum_list sequence \<ge> m"
  sorry

end