theory mi16096_Milena_Stojic_Binommial_coefficients
  imports Complex_Main

begin
text
\<open>
  Teorija u kojoj definišemo binomni koeficijent i posle dokazujemo
  sve važne identitete sa njima.
\<close>

text
\<open>
  Pre nego što definišemo pojam binomnog koeficijenta, neophodan
  nam je pojam faktorijela (proizvoda uzastopnih prirodnih brojeva)
\<close>
primrec fact :: "nat \<Rightarrow> nat" where
"fact 0 = 1" |
"fact (Suc n) = (Suc n) * (fact n)"


value "fact 5"

text
\<open>
  Iako ih nećemo koristiti u ovom fajlu, ovde ćemo definisati
  i proizvod uzastopnih parnih ili uzastopnih neparnih brojeva.
  (proizvod prvih n neparnih brojeva)
\<close>
primrec fact2 :: "nat \<Rightarrow> nat" where
"fact2 0 = 1" |
"fact2 (Suc n) = (2 * (Suc n) - 1) * (fact2 n)"

value "fact2 3"

lemma theorem_for_factorial:
  fixes n::nat
  assumes "n \<ge> 1"
  shows "n * fact(n - 1) = fact(n)"
  using assms
proof (induction n rule: nat_induct_at_least)
  case base
  then show ?case by simp
next
  case (Suc n)
  have "fact (Suc n) = (Suc n) * fact(n)"
    unfolding fact_def
    by simp
  then show ?case by simp
qed



text
\<open>
  Sada definišemo binomni koeficijent.
\<close>
definition binomm_core :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"binomm_core n k = ((fact n) div (((fact k)) * (fact (n - k))))"

definition binomm :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"binomm n k =  (if n \<ge> k then (binomm_core n k) else 0)" \<comment> \<open>Ne dozvoljavamo nekorektne argumente.\<close>

value "binomm 5 5"
value "binomm 5 0"
value "binomm 5 2" 
value "binomm 5 3" \<comment> \<open>Na ovom primeru važi svojstvo da je (n k) i (n n-k) jednako. I to je identitet koji ćemo dokazivati za sve binomne koeficijente generalno.\<close>


text
\<open>
  Sada ćemo dokazati uslov simetričnosti za binomne koeficijente.
\<close>

lemma binomm_symmetry:
  assumes "k \<le> n"
  shows "(binomm n k) = (binomm n (n - k))"
proof-
  have p:"k = n - (n - k)"
    using assms 
    by simp
  have "binomm n k = (fact n) div ((fact k) * (fact (n - k)))"
    using assms
    unfolding binomm_def binomm_core_def
    by simp
  also have "\<dots> = (fact n) div ((fact (n - (n - k))) * (fact (n - k)))"
    using p
    by simp
  also have "\<dots> = (fact n) div ((fact (n - k)) * (fact (n - (n - k))))"
    by (subst mult.commute, rule refl)
  also have "\<dots> = binomm n (n - k)"
    unfolding binomm_def binomm_core_def
    by simp
  finally show ?thesis .
qed


lemma pom:
  fixes a::nat
  assumes "e \<noteq> 0"
  assumes "(a * b) mod e = 0"
  assumes "(c * d) mod e = 0"
  shows "((a * b) div e) + ((c * d) div e) = (a * b + c * d) div e"
  using assms by auto
(*
lemma pom'':
  fixes n::nat
  assumes "n \<ge> 1"
  assumes "n \<ge> k"
  shows "(fact n) mod ((fact k) * (fact (n - k))) = 0"
  using assms
proof (induction n rule: nat_induct_at_least)
  case j:base
  then show ?case
  proof (cases "k = 0")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using assms(2) sledgehammer
      by (metis One_nat_def Suc_leI diff_diff_cancel diff_is_0_eq' fact.simps(1) j.prems le_less mod_self mult.right_neutral zero_less_diff)
  qed
next
  case (Suc n)
  then show ?case 

qed*)

lemma addition_formula:
  assumes "k \<ge> 1"
  assumes "n \<ge> 2"
  assumes "k \<le> n - 1"
  shows "(binomm n k) = (binomm (n - 1) (k - 1)) + (binomm (n - 1) k)"
proof-
  have s1: "binomm (n - 1) (k - 1) = (fact (n - 1)) div ((fact (k - 1)) * (fact (n - 1 - (k - 1))))"
    (is "?b1 = ?e1")
    using assms
    unfolding binomm_core_def binomm_def
    by simp
  have s2: "(binomm (n - 1) k) = (fact (n - 1)) div ((fact k) * (fact ((n - 1) - k)))"
    (is "?b2 = ?e2")
    using assms
    unfolding binomm_core_def binomm_def
    by simp
  have utility: "(n - k) * fact (n - k - 1) = fact (n - k)"
    using assms theorem_for_factorial
    unfolding fact_def
    sledgehammer
    using Suc_diff_le by fastforce
  from s1 s2 have "?b1 + ?b2 = ?e1 + ?e2"
    by simp
  also have "\<dots> = (fact (n - 1)) div ((fact (k - 1) * (fact (n - k)))) + ?e2"
    using assms
    by simp
  also have "\<dots> = (k * fact(n - 1)) div ((k * fact (k - 1) * (fact (n - k)))) +
              ((n - k) * (fact (n - 1))) div ((n - k) * (fact k) * (fact ((n - 1) - k)))"
    using assms field_simps
    by simp
  also have "\<dots> = (k * fact(n - 1)) div (k * fact (k - 1) * (fact (n - k))) +
              ((n - k) * (fact (n - 1)) div ((fact k) * (n - k) * (fact ((n - 1) - k))))" 
    by (subst mult.commute[of "(fact k)" "(n - k)"], rule refl)
  also have "\<dots> = (k * fact(n - 1)) div (k * fact (k - 1) * (fact (n - k))) +
              ((n - k) * (fact (n - 1)) div ((fact k) * ((n - k) * fact (n - k - 1))))"
    using field_simps
    by simp
  also have "\<dots> = (k * fact(n - 1)) div ((fact k) * (fact (n - k))) +
              ((n - k) * (fact (n - 1)) div ((fact k) * (fact (n - k))))"
    using assms theorem_for_factorial utility
    unfolding fact_def
    by simp
  also have "\<dots> = (fact(n - 1)) * (k div ((fact k) * (fact (n - k)))) +
               (fact (n - 1)) * ((n - k)  div ((fact k) * (fact (n - k))))"
    using assms 
    sorry
qed
  
end