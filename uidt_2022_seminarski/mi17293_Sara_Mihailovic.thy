theory mi17293_Sara_Mihailovic
  imports Main Complex_Main

begin

text\<open>
Link: https://imomath.com/srb/zadaci/2003_mmo.pdf?fbclid=IwAR3RtxCoFki3-9ZTLy2CXBK01tUx0zluEsvwNAdVCH5mB-HWwwzU-GqjlSQ
Algebra: 2. zadatak
Find all pairs (m, n) of positive integers such that m^2 / (2*m*n^2 - n^3 +1)
is a positive integer.
Answer: The answer is (m, n) = (2l, 1), (m, n) = (l, 2l) and (m, n) = (8*l^4 −l, 2l), for any l.
\<close>

(* Prvi deo *)
lemma
  fixes m n :: nat
  assumes "m>0 \<and> n>0" "m^2 / (2*m*n^2 - n^3 +1) >0"
  shows "\<exists> l. (m = 2*l \<and> n = 1) \<or> (m = l \<and> n = 2*l) \<or> (m = 8*l^4 - l \<and> n = 2*l)"
  sorry

lemma
  fixes m n :: nat
  assumes "m>0 \<and> n>0"
  assumes "m = 2*l" "n=1"
  shows "m^2 / (2*m*n^2 - n^3 +1) >0"
  using assms
  by simp

lemma
  fixes m n :: nat
  assumes "m>0 \<and> n>0"
  assumes "m = l" "n=2*l"
  shows "m^2 / (2*m*n^2 - n^3 +1) >0"
  using assms
  by simp

lemma
  fixes m n :: nat
  assumes "m>0 \<and> n>0"
  assumes "m = 8*l^4 - l" "n = 2*l"
  shows "m^2 / (2*m*n^2 - n^3 +1) >0"
  using assms
  by simp
  
  

end