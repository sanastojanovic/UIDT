theory mi15263_Milos_Krsmanovic

imports Complex_Main "HOL-Library.Multiset"


begin

text\<open>
  Prvi seminarski u okviru kursa Uvod u interaktivno dokazivanje teorema
  Profesor: dr Filip Maric
  Asistent: dr Sana Stojanovic Djurdjevic
  Student:  Milos Krsmanovic


  Medjunarodna matematicka olimpijada 1995. god.

  Problem 2:
  Neka su a, b i c pozitivni realni brojevi, takvi da je 
  a * b * c = 1. Dokazati da vazi naredno tvrdjenje:

   1/(a^3*(b + c)) + 1/(b^3*(c + a) + 1/(c^3*(a + b)) \<ge> 3/2
\<close>

(* Prvi seminarski: formulacija problema*)

lemma nejednakost: 
  fixes a b c :: real
  assumes "a * b * c = 1"
  shows "1 / (a^3 * (b + c)) + 
         1 / (b^3 * (c + a)) + 
         1 / (c^3 * (a + b)) \<ge> 3/2"
  sorry

lemma metod_smene:
  fixes a b c x y z :: real
  assumes "x=1/a" "y=1/b" "z=1/c"
  shows "1 / (a^3 * (b + c)) + 
         1 / (b^3 * (c + a)) + 
         1 / (c^3 * (a + b)) = 
         x^3/(x * y * z * (1/y + 1/z)) + 
         y^3/(x * y * z * (1/z + 1/x)) + 
         z^3/(x * y * z * (1/x + 1/z))"
  sorry

lemma metod_smene_2:
  fixes a b c x y z :: real
  assumes "1 / (a^3 * (b + c)) + 
         1 / (b^3 * (c + a)) + 
         1 / (c^3 * (a + b)) = 
         x^3/(x * y * z * (1/y + 1/z)) + 
         y^3/(x * y * z * (1/z + 1/x)) + 
         z^3/(x * y * z * (1/x + 1/z))"
  shows "x^3/(x * y * z * (1/y + 1/z)) + 
         y^3/(x * y * z * (1/z + 1/x)) + 
         z^3/(x * y * z * (1/x + 1/z)) =
         x^2/(y + z) + y^2/(z + x) + z^2/(x + y)"
  sorry


end