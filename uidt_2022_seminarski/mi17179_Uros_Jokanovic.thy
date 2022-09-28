  
text\<open>Algrebra A7 problem
   https://www.imo-official.org/problems/IMO2008SL.pdf

17. Prove that for any four positive real numbers a,b,c,d the inequality
   (a - b) * (a - c) / (a + b + c) + (b - c) * (b - d) / (b + c + d) 
   + (c - d) * (c - a) / (c + d + a) + (d - a) * (d - b) / (d + a + b) 
   \<ge> 0 
   holds. Determine all cases of equality.
\<close>

theory mi17179_Uros_Jokanovic
  imports Main HOL.Num HOL.NthRoot Complex_Main HOL.Set HOL.Real

begin

text\<open>Prvi seminarski: formulisanje problema\<close>

lemma formulacija: 
  fixes "a" "b" "c" "d" :: real
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  shows "(a - b) * (a - c) / (a + b + c)
       + (b - c) * (b - d) / (b + c + d)
       + (c - d) * (c - a) / (c + d + a)
       + (d - a) * (d - b) / (d + a + b)
       \<ge> 0"
  using assms
  sorry

text\<open>Drugi seminarski: raspisivanje resenja formulisanog problema\<close>