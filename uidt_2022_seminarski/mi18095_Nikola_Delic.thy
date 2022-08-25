theory mi18095_Nikola_Delic
  imports Complex_Main
begin

text\<open>
Link: https://www.imo-official.org/problems/IMO2019SL.pdf
Number Theory: A1

Let Z be the set of integers. Determine all functions f : Z -> Z such that, for all
  integers a and b,
            f (2*a) + 2*f(b) = f(f(a + b)).
 
Answer: The solutions are f (n) = 0 and f (n) = 2*n + K for any constant K \<in> Z.

\<close>
(* 1. Seminarski*)

lemma final:
  fixes a b::int
  assumes "\<forall>a. \<forall> b. f(2*a) + 2*f(b) = f(f(a+b))"
  shows "\<forall> n.\<exists> K. f n = 0 \<or> f n = 2 * n + K"
  sorry

(*2. seminarski*)
lemma help1:
  fixes a b n::int
  assumes "\<forall>a. \<forall> b. f(2*a) + 2*f(b) = f(f(a+b))"
  shows "\<exists> M. \<exists>K. f n = M*n + K"
  by (metis add_0 mult_zero_left)

lemma help2:
  fixes a b n M K::int
  assumes "\<forall>a. \<forall> b. f(2*a) + 2*f(b) = f(f(a+b))""\<exists> M. \<exists>K. f n = M*n + K"
  shows "\<exists>M . \<exists>K. M*2*a + K + 2*(M*b + K) = M*(M*(a+b) + K) + K"
  by (metis add_0 mult_zero_left mult_zero_right)


lemma help3:
  fixes M K::int
  assumes "M*2*a + K + 2*(M*b + K) = M*(M*(a+b) + K) + K"
  shows"(2 - M)*(M*(a+b) + K) = 0"
  using assms
proof-
  assume"M*2*a + K + 2*(M*b + K) = M*(M*(a+b) + K) + K"
  then have "M*2*a + 2*(M*b + K) = M*(M*(a+b) + K)" by auto
  then have "2*M*(a+b) + 2*K = M*(M*(a+b) + K)" by (simp add: ring_class.ring_distribs(1))
  then have "2*(M*(a+b) + K) - M*(M*(a+b) + K) = 0" by simp
  then have "(2 - M)*(M*(a+b) + K) = 0" by (simp add: left_diff_distrib)
  then show ?thesis by auto
qed

lemma final1:
  fixes a b::int
  assumes "\<forall>(a::int). \<forall> b. f(2*a) + 2*f(b) = f(f(a+b))"
  shows "\<forall> n.\<exists> K. f n = 0 \<or> f n = 2 * n + K"
  using assms
proof-
  assume "\<forall>a. \<forall> b. f(2*a) + 2*f(b) = f(f(a+b))"
  then have "\<exists> M. \<exists>K. f n = M*n + K" using help1 by (metis add_0 mult_zero_left)
  
  then have "\<exists>M. \<exists>K. M*2*a + K + 2*(M*b + K) = M*(M*(a+b) + K) + K" using `\<forall>a. \<forall> b. f(2*a) + 2*f(b) = f(f(a+b))` help2 by blast
  then obtain M K where "M*2*a + K + 2*(M*b + K) = M*(M*(a+b) + K) + K" by auto
  then have "(2 - M)*(M*(a+b) + K) = 0" using assms using help3 by presburger
  then have "M = 2 \<or> M*(a+b) + K = 0" by auto
  then show ?thesis by (metis add.commute diff_add_cancel)
  
qed

end