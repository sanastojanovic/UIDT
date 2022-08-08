theory mi17300_Katarina_Nikolic
  imports Complex_Main HOL.Real
begin 

text\<open>
Link: https://www.imo-official.org/problems/IMO2016SL.pdf
Algebra A1

Let a, b, and c be positive, real numbers such that min{ab,bc,ca} >= 1. Prove that:
((a^2 + 1)*(b^2 + 1)*(c^2 + 1))^(1/3) \<le> ((a + b + c)/3)^2 + 1
\<close>

declare [[quick_and_dirty = true]]
term root
term Min

lemma pomocna_1: 
  fixes x y :: real
  assumes "x*y \<ge> 1"
  shows "(x^2 + 1)*(y^2 + 1) \<le> (1 + ((x+y)/2)^2)^2"
  sorry

lemma glavna:
  fixes a b c ::real
  assumes "Min {a*b, b*c, c*a} \<ge> 1"
  shows "root 3 ((a^2 + 1)*(b^2 + 1)*(c^2 + 1)) \<le> 1 + ((a + b + c)/3)^2"
  sorry
end

