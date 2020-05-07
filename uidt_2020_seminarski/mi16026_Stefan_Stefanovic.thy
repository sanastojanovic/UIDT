theory mi16026_Stefan_Stefanovic
  imports Main
begin
typ nat

theorem zadatak:
  fixes x y m n :: nat
  assumes "x>(0::nat)"
  assumes "y>(0::nat)"
  shows "\<forall>xy.\<not>(\<exists>mn.(m*m=x*x+y*y \<and> n*n=x*x+(4::nat)*y*y))"
  
