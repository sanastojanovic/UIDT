theory mi16119_Dusica_Golubovic
  imports Main
begin
(*2018 internacionalna olimpijada
  N5

Cetiri pozitivna prirodna broja 
za koja vazi jednakost x*y - z*t = x+y = z + t
Da li oba broja x*y i z*t mogu biti savrseni kvadrati?
Pokazujemo da ne moze da vazi da se i x*y i z*t 
ne mogu napisati kao x*y = a^2 i z*t = c^2
gde su a>0 i c > 0 

*)

lemma sem:
  fixes x y z t a c :: nat
  assumes "c > 0" "a > 0"
  assumes "x*y - z*t = x + y"
  assumes "x*y - z*t = z + t"
  shows "\<not>(x*y = a^2) \<or> \<not>(z*t = c^2)"
  sorry
end