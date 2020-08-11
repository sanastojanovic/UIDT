theory mi16136_Krizan_Andjela
  imports Complex_Main
begin

text \<open>
Zadatak 4, drugi razred sa linka: https://imomath.com/srb/zadaci/RS_2016_republicko_resenja.pdf
Tekst:
Ako su m i n prirodni brojevi za koje vazi 7*m^2 + 7*m + 2 = n^2,
dokazati da je broj n + 1 jednak zbiru kvadrata dva uzastopna prirodna broja.
\<close>


lemma zadatak:
  fixes m n a b :: nat
  assumes "7*m^2 + 7*m + 2 = n^2" "b = a + 1"
  shows "n + 1 = a^2 + b^2"
  sorry
  
end