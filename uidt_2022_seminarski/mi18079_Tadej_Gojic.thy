theory mi18079_Tadej_Gojic
  imports Main
          HOL.Real
begin

text\<open>
  Link : https://www.imo-official.org/problems/IMO2020SL.pdf 
  Algebra : A8
  Zadatak: Neka je R^+ skup pozitivnih realnih brojeva. Odrediti sve funkcije f: R^+ -> R^+ takve da za svaka dva pozitivna realna broja x i y vazi sledece:
    f(x + f(x*y)) + y = f(x)*f(y) + 1
\<close> 


lemma konacna_teorema:
  fixes f :: "real \<Rightarrow> real"
  fixes x :: "real"
  fixes y :: "real"
  assumes "x > 0"
  assumes "y > 0"
  assumes "\<forall> (a::real) > 0. f(a) > 0"
  assumes "f(x + f(x*y)) + y = f(x)*f(y) + 1"
  shows "f(x) = x + 1" using assms 
  sorry
end

