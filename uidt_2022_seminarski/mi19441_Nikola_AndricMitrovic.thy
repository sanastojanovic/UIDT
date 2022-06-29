theory mi19441_Nikola_AndricMitrovic
  imports HOL.Real HOL.Transcendental Main
begin

text\<open>
Link: https://www.imo-official.org/problems/IMO2020SL.pdf
Algebra: A4

Let a, b, c, d be four real numbers such that a >= b >= c >= d > 0 and a + b + c + d = 1.
Prove that (a + 2b + 3c + 4d) * a^a * b^b * c^d * d^d < 1.
\<close>



fun dot_product :: "real list \<Rightarrow> real list \<Rightarrow> real" where
"dot_product [] [] = 1" |
"dot_product (x # xs) (y # ys) = x*y + dot_product xs ys"

fun squared_weight :: "real list \<Rightarrow> real list \<Rightarrow> real" where
"squared_weight [] [] = 1" |
"squared_weight (x # xs) (y # ys) = x powr y + squared_weight xs ys"


lemma weighted_am_gm_ineq[simp]:
  fixes ws :: "real list"
  fixes xs :: "real list"
  assumes "length xs = length ws"
  assumes "length xs \<ge> 1"
  assumes "\<forall> w \<in> set ws. w \<ge> 0"
  shows "squared_weight xs ws powr (1 / sum_list ws) \<le> dot_product xs ws / sum_list ws"
  using assms
  apply (induction xs)
   apply simp
  apply (induction ws)
   apply simp
  sorry

lemma powr_le_sq[simp]:
  fixes a b c d :: real
  assumes "a + b + c + d = 1"
  assumes "a \<ge> b"
  assumes "b \<ge> c"
  assumes "c \<ge> d"
  assumes "d > 0"
  shows "(a powr a)*(b powr b)*(c powr c)*(d powr d) \<le> a*a + b*b + c*c + d*d"
  using assms
  sorry

lemma pom1[simp]:
  fixes a b c d :: real
  assumes "a + b + c + d = 1"
  assumes "a \<ge> b"
  assumes "b \<ge> c"
  assumes "c \<ge> d"
  assumes "d > 0"
  shows "(a + 2*b + 3*c + 4*d)*(a*a + b*b + c*c + d*d) \<le> (a + b + c + d) powr 3"
  sorry



lemma zadatak:
  fixes a b c d :: real
  assumes "a + b + c + d = 1"
  assumes "a \<ge> b"
  assumes "b \<ge> c"
  assumes "c \<ge> d"
  assumes "d > 0"
  shows "(a + 2*b + 3*c + 4*d)*(a powr a)*(b powr b)*(c powr c)*(d powr d) < 1"
  using assms
  sorry


end
