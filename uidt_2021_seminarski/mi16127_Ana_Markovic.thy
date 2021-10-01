theory mi16127_Ana_Markovic
imports Complex_Main

begin

\<comment> 
\<open> https://www.imo-official.org/problems/IMO2010SL.pdf 
  Algebra A4
\<close>

(* ======= definisanje oblika x_i ======================*)
(* pomeranje indksa:
  x1 = 1
  x_2k = -x_k
    2k = n
    k = n / 2
  x_2k-1 = (-1)^(k+1)x_k
    2k-1 = n
    k = (n+1) / 2
*)
fun x_i_def :: "nat \<Rightarrow> int" where
"x_i_def n = ( if n = 0 then 0
               else if n = 1 then 1
               else if n mod 2 = 0 
                then (-1 * (x_i_def (n div 2))) 
               else 
                (-1)^((n + 1) div 2 + 1) * (x_i_def ((n + 1) div 2)))"

value "x_i_def 1"
value "x_i_def 2"
value "x_i_def 3"
value "x_i_def 4"
value "x_i_def 5"

(* ================= definisana suma x_i ================ *)

primrec sum_of_x_i :: "nat \<Rightarrow> int" where
"sum_of_x_i 0 = 0" |
"sum_of_x_i (Suc n) = x_i_def (Suc n) + sum_of_x_i n"

value "sum_of_x_i 5"

(* definisane jednakosti 
   x_4k-3 = -x_4k-2 
   x_4k-1 = x_4k
*)

(* ============== Dokaz X_4k-3 = -X_4k-2 ================= *)

lemma mod2_1:
  fixes n :: nat
  assumes "n \<ge> 1"
  shows "(4*n - 3) mod 2 = 1"
  using assms
  by presburger

lemma div2_1:
  fixes n :: nat
  assumes "n \<ge> 1"
  shows "2*n - 1 = (4*n - 2) div 2"
  using assms
  by presburger

lemma mod2_2:
  fixes n :: nat
  assumes "n \<ge> 1"
  shows "(4*n - 2) mod 2 = 0"
  using assms
  by presburger

lemma "4_k_3":
  fixes n :: nat
  assumes "n \<ge> 1"
  shows "((4*n-3)+1) div 2 = 2*n-1"
  using assms
proof -
  have "((4*n-3)+1) div 2 = (4*n-3+1) div 2"
    by simp
  also have "... = (4*n-2) div 2"
    by simp
  also have "... = 2*n - 1"
    by simp
  finally show ?thesis by simp
qed

lemma equation_4k_3:
  fixes k :: nat
  assumes "k \<ge> 1"
  shows "x_i_def (4*k-3) = (-1)*x_i_def (4*k-2)"
  using assms
proof (cases "(4*k-3) mod 2 = 0")
  case True
  then show ?thesis using mod2_1 assms by simp
next
  case False
  then have "x_i_def (4*k-3) = (-1)^(((4*k - 3) + 1) div 2 + 1) * (x_i_def (((4*k - 3) + 1) div 2))"
    using assms False x_i_def.simps by simp
  also have "... = (-1)^((2*k-1)+ 1) * (x_i_def (2*k-1))"
    using "4_k_3" assms by presburger
  also have "... = (-1)^((2*k-1)+ 1) * (x_i_def ((4*k-2) div 2))"
    using div2_1 assms False x_i_def.simps by metis
  also have "... =  (-1)^((2*k-1)+ 1)*(-1)*x_i_def(4*k-2)"
    using mod2_2 assms x_i_def.simps
    by (smt (z3) bits_1_div_2 minus_mult_minus mod_eq_self_iff_div_eq_0)
  also have "... = (-1)^((2*k-1)+ 2)*x_i_def(4*k-2)"
    by simp
  also have "... = (-1)*x_i_def(4*k-2)"
    using assms x_i_def.simps by simp
  finally show ?thesis using assms x_i_def.simps by simp
qed

lemma equation_4k_1:
  shows "x_i_def (4*k-1) = x_i_def (4*k)"
  sorry

lemma equation_k_1:
  assumes "k\<ge>1"
  assumes "k mod 2 = 0"
  shows "x_i_def (k+1) = x_i_def (4*k+1)"
  using assms
  sorry

(* =======================  definisane parcijalnih suma ====================== *)
definition S_k :: "nat \<Rightarrow> int" where
"S_k n = (\<Sum>i\<le>n. (x_i_def i))"

definition S_4k :: "nat \<Rightarrow> int"where
"S_4k n = (\<Sum>i\<le>n. (
    (x_i_def (i*4-3) + x_i_def (i*4-2)) + 
    (x_i_def (i*4-1) + x_i_def (i*4))
  ))"

definition S_4k_2 :: "nat \<Rightarrow> int" where
"S_4k_2 n = (S_4k n 
             + x_i_def (4*n+1) 
             + x_i_def (4*n+2))"

definition S_4k_4 :: "nat \<Rightarrow> int" where
"S_4k_4 n = S_4k (n+1)"

lemma S_4k_4_l :
  shows "S_4k (n+1) = (S_4k n 
          + x_i_def (4*n+1)
          + x_i_def (4*n+2)
          + x_i_def (4*n+3)
          + x_i_def (4*n+4))"
  sorry

definition S_4k_3 :: "nat \<Rightarrow> int" where
"S_4k_3 n = (S_4k_2 n + S_4k_4 n) div 2"

(* S_4k = 2*S_k *)
lemma S_4k_eq_2S_k:
  assumes "n\<ge>1"
  shows "S_4k n = 2 * S_k n"
  using assms
  sorry

(* S_4k+2 = S_4k *)
lemma S_4k_eq_S_4k_2:
  assumes "n\<ge>1"
  shows "S_4k_2 n = S_4k n"
  using assms
  sorry

(* Pokazivanje da su
   S_4k \<ge> 0
   S_4k+1 \<ge> 0
   S_4k+2 \<ge> 0
   S_4k+3 \<ge> 0
   S_4k+4 \<ge> 0 
   pod pretpostavkom da je S_k \<ge> 0
*)

lemma S_4k_nonegativ:
  fixes k::nat
  assumes "k \<ge> 1"
  assumes "n \<le> 4*k"
  assumes "n\<ge>1"
  assumes "\<forall> n. S_k n \<ge> 0"
  shows "S_4k n \<ge> 0"
  using assms 
proof-
  have "S_4k n = 2 * S_k n"
    using S_4k_eq_2S_k `n \<ge> 1` by simp
  also have "... \<ge> 0"
    using assms by simp
  finally show ?thesis .
qed 

lemma S_4k_2_nonegativ:
  fixes k::nat
  assumes "k \<ge> 1"
  assumes "n \<le> 4*k"
  assumes "n\<ge>1"
  assumes "\<forall> n. S_k n \<ge> 0"
  shows "S_4k_2 n \<ge> 0"
  using assms 
proof-
  have "S_4k_2 n = S_4k n"
    using S_4k_eq_S_4k_2 `n \<ge> 1` by simp
  also have "... \<ge> 0"
    using assms S_4k_nonegativ by simp
  finally show ?thesis .
qed 

lemma S_4k_4_nonegativ:
  fixes k::nat
  assumes "k \<ge> 1"
  assumes "n \<le> 4*k"
  assumes "\<forall> n. S_k n \<ge> 0"
  shows "S_4k_4 n \<ge> 0"
  using assms 
proof -
  have "S_4k_4 n = S_4k (n+1)"
    using S_4k_4_def by simp
  also have "... = 2 * S_k (n+1)"
    using S_4k_eq_2S_k by simp
  also have "... \<ge> 0"
    using assms `\<forall> n . S_k n \<ge> 0` by simp
  finally show ?thesis .
qed

lemma S_4k_3_nonegativ:
  fixes k::nat
  assumes "k \<ge> 1"
  assumes "n \<le> 4*k"
  assumes "n\<ge>1"
  assumes "\<forall> n. S_k n \<ge> 0"
  shows "S_4k_3 n \<ge> 0"
  using assms
proof -
  have "S_4k_3 n = (S_4k_2 n + S_4k_4 n) div 2"
    using S_4k_3_def by simp
  also have "... \<ge> 0"
    using 
      S_4k_2_nonegativ 
      S_4k_4_nonegativ assms 
      `\<forall> n .S_k n \<ge> 0`
    using S_4k_4_def assms by force
  finally show ?thesis .
qed

definition S_4k_1 :: "nat \<Rightarrow> int" where
"S_4k_1 n = S_4k n + x_i_def (4*n+1)"

lemma sum_k:
  fixes k::nat
  assumes "k \<ge> 1"
  shows "(2*S_k k) \<ge> 0"
  using assms
proof (induction k rule: nat_less_induct)
  case (1 k)
  thm 1
  show ?case
    proof (cases "k=1")
      case True
    then show ?thesis 
    proof -
      have "2*S_k k = S_4k k"
        using S_4k_eq_2S_k[symmetric]  `k=1` by simp
      also have "S_4k k = x_i_def 1 +  x_i_def 2 +  x_i_def 3 +  x_i_def 4"
        using S_4k_def `k=1` by simp
      also have "... \<ge> 0"
        by simp
      finally show ?thesis .
    qed
    next
      case False
      then show ?thesis 
      proof -
        have "S_4k k = 2 * S_k k"
          using S_4k_eq_2S_k assms 
          using "1.prems" 
          by blast
        then show ?thesis sorry
      qed
   qed
qed


end