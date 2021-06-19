theory mi17063_Luka_Vujcic
  imports Complex_Main
begin
text\<open>
  https://www.imo-official.org/problems/IMO2013SL.pdf
  Zadatak: Number theory N2
  Tekst zadatka: Dokazati da za svaka dva prirodna broja k i n postoji
  k prirodnih brojeva m1,m2,...,mk (ne obavezno razlicitih) takvih da je
  1+ (2^k-1)/n=(1+1/m1)(1+1/m2)...(1+1/mk)
\<close>
(*Formulacija leme*)
lemma
  fixes k n::nat
  assumes "k>0" "n>0" 
  shows "\<exists> m::nat list. prod_list m \<noteq> 0 \<and> length m=k \<and> 1+ (2^k-1) / n=sum_list (map (\<lambda> x. 1+1 / x) m)"
  using [[show_types]]
  sorry
end