theory Seminarski
  imports Main HOL.Real "HOL-ex.Sqrt" "HOL-ex.Sqrt_Script" 

begin

text \<open>
Link: https://www.imo-official.org/problems/IMO2006SL.pdf
A5. Neka su a b i c stranice trougla. Pokazati:
sqrt (b + c - a) / (sqrt b + sqrt c - sqrt a) + sqrt (c + a - b) / (sqrt c + sqrt a - sqrt b) + sqrt (a + b - c) / (sqrt a + sqrt b - sqrt c) <= 3
\<close>

definition sides_of_triangle :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
"sides_of_triangle a b c \<longleftrightarrow> (a < b + c) \<and> (b < a + c) \<and> (c < a + b) \<and> a > 0 \<and> b > 0 \<and> c > 0"

definition triang_ineq :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
"triang_ineq p q r \<longleftrightarrow> p + q > r"

lemma DenPositive:
  assumes "p > 0" "q > 0" "r > 0"
  assumes "triang_ineq p q r"
  shows "sqrt p + sqrt q - sqrt r > 0"
  using assms
  unfolding triang_ineq_def
proof-
  have "p + q > r"
    using assms(4) triang_ineq_def by auto
  from this have "sqrt p + sqrt q > sqrt r"
    by (smt (z3) assms(1) assms(2) real_sqrt_less_mono sqrt_add_le_add_sqrt)
  from this show ?thesis
    by simp
qed

lemma MainProblem:
  fixes a b c :: "real"
  assumes "a > 0" "b > 0" "c > 0" "a + b > c"
  assumes "triang_ineq a b c" "triang_ineq a c b" "triang_ineq b c a"
  shows "sqrt(b + c - a) / (sqrt b + sqrt c - sqrt a)
        + sqrt (c + a - b) / (sqrt c + sqrt a - sqrt b)
        + sqrt(a + b - c)/(sqrt a + sqrt b - sqrt c) 
        \<le> (3::real)" (is "?e1/?x + ?e2/?y + ?e3/?z \<le> (3::real)")
  using assms
  unfolding triang_ineq_def
  
proof-
  have "?x > 0"
    using assms
    using DenPositive by blast
  have "?y > 0"
    using assms
    using DenPositive by fastforce
  have "?z > 0"
    using assms
    using DenPositive by auto

  show ?thesis sorry
    
  
qed
  
  

end