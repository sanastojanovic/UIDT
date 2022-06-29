theory mi17144_Jovana_Markovic
  imports Main Complex_Main

begin

text\<open>
Link: https://www.imo-official.org/problems/IMO2020SL.pdf
Algebra: A1
Let n be a positive integer, and set N “ 2n. Determine the smallest real
number an such that, for all real x,
(x^(2*N) + 1) / 2 \<le> (an*(x-1)^2 + x)^N
Answer: an=N/2
\<close>

lemma A1:
  fixes  n :: nat and N::nat and x::real
  assumes "n>0" "x>0" "N = 2^n" 
  shows "\<forall> x. (x^(2*N) + 1) / 2 \<le> (N/2*(x-1)^2 + x)^N"
        "\<not>(\<exists> bn.  \<forall> x. (x^(2*N) + 1) / 2  \<le> (bn*(x-1)^2 + x)^N \<and> bn < N / 2)"
  using assms
  sorry

end