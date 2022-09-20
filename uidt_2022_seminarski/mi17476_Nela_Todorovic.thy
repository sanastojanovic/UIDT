theory mi17476_Nela_Todorovic
imports Complex_Main
begin

text \<open>

https://www.imo-official.org/problems/IMO2009SL.pdf
Algebra A4 problem

\<close> 

lemma glavna:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a*b + b*c + c*a \<le> 3 * a*b*c"
  shows "sqrt((a^2 + b^2)/(a + b)) + sqrt((b^2 + c^2)/(b + c)) + sqrt((c^2 + a^2)/(c + a)) + 3
         \<le> sqrt(2) * (sqrt(a + b) + sqrt(b + c) + sqrt(c + a))" 
  sorry


end