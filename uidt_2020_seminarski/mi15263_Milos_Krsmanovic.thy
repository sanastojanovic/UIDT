theory mi15263_Milos_Krsmanovic
  imports Complex_Main
begin

text \<open>
Prvi dan, zadatak 1.
Link: https://imomath.com/srb/zadaci/BIH_2015_bihmo_resenja.pdf
Formulacija:
Odrediti najmanju mogucu vrednost izraza
(a+1)/(a*(a+2)) + (b+1)/(b*(b+2)) + (c+1)/(c*(c+2))
za pozitivne realne brojeve a,b i c, ako je a+b+c\<le>3
\<close>

(*f-ja za izracunavanje vrednosti izraza kada su sva tri broja a,b,c realna*)
fun vrednost_izraza::"real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
"vrednost_izraza a b c = (a+1)/(a*(a+2)) + (b+1)/(b*(b+2)) + (c+1)/(c*(c+2))"

(*Provera vrednosti izraza za neke realne, pozitivne brojeve, za koje vazi trazeno svojstvo*)
value "vrednost_izraza 0.5 1 1"


(*Predstavljanje svakog od sabiraka leve strane na drugi nacin*)
lemma "(a+1)/(a*(a+2)) = 1/2*(1/a + 1/(a+2))"
  sorry

lemma "(b+1)/(b*(b+2)) = 1/2*(1/b + 1/(b+2))"
  sorry

lemma "(c+1)/(c*(c+2)) = 1/2*(1/c + 1/(c+2))"
  sorry

lemma 
  fixes a b c :: real
  shows "(a+1)/(a*(a+2)) + (b+1)/(b*(b+2)) + (c+1)/(c*(c+2)) = 1/2*(1/a + 1/b + 1/c) +1/2*(1/(a+2) + 1/(b+2) + 1/(c+2))"
  sorry

end