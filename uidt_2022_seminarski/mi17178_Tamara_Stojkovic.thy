theory mi17178_Tamara_Stojkovic
   imports Main Complex_Main
begin 

text \<open>
Link: https://www.imo-official.org/problems/IMO2015SL.pdf
Zadatak:Algebra A4
Tekst:
Find all functions f : \<real> \<rightarrow> \<real> satisfying the equation
f(x + f(x+y)) + f(xy) = x + f(x+y)+ yf(x)
for all real numbers x and y.

Odgovor:
There are two functions, namely the identity function(x\<rightarrow>x) and x \<rightarrow> 2 - x
\<close>



theorem concluding_theorem:
  fixes x::real
  fixes y::real 
  fixes f::" real \<Rightarrow> real"
  assumes "\<forall> x y. (f (x + f (x+y)) + f (x*y) = x + f (x+y) + y * (f x))"
  shows "(\<forall> x. f x = x) \<or> (\<forall> x. f x = 2 - x) "
  using assms
  sorry







  
