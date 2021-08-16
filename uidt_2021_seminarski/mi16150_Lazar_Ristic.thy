theory mi16150_Lazar_Ristic
  imports Main
begin

text \<open>

Link ka seminarskom zadatku: https://www.imo-official.org/problems/IMO2013SL.pdf
Algebra A4 zadatak


Tekst seminarskog zadatka: 

Neka je n pozitivan ceo broj i niz a1, ..., an niz pozitivnih celih brojeva.
Periodicno produziti niz do beskonacnog a1, a2, ... definisanjem a_n+i = ai,
za svako i >= 1.

Ako je

a1 <= a2 <= ... <= an <= a1 + n 

i

a_ai <= n+i-1, za i=1,2,...,n

dokazati da je

a1 + ... + an <= n^2.


\<close>

primrec suma_niza :: "nat list \<Rightarrow> nat" where
"suma_niza [] = 0" | 
"suma_niza (x#xs) = x + suma_niza xs"

primrec niz_veci_od_nule :: "nat list \<Rightarrow> bool" where
"niz_veci_od_nule [] = True" |
"niz_veci_od_nule (x#xs) = ((x\<ge>0) & (niz_veci_od_nule xs))"

fun "a_ai_manje" :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
"a_ai_manje 0 _ _ _ = True" |
"a_ai_manje rpt n l i = (((l ! (l ! i)) \<le> n+i-1) & (a_ai_manje (rpt-1) n l (i+1)))"
(* rpt predstavlja pomocnu promenljivu koja prekida rad f-je *)

value "a_ai_manje 4 4 [1,2,3,4,5] 0"

value "niz_veci_od_nule [1,2,3]"
value "suma_niza [1,2,3]"
value "sorted [1::nat,2,3]"
value "[1,2::nat,3] ! 2"

lemma "zadatak":
  fixes n :: nat and A :: "nat list"
  assumes "n > 0" and "niz_veci_od_nule A"
  assumes "sorted A"
  assumes "(A ! n-1) \<le> (A ! 0) + n"
  assumes "a_ai_manje (n-1) (n-1) A 0"
  shows "suma_niza A \<le> n*n"
  sorry

end