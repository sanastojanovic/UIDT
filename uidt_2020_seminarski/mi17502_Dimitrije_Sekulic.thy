theory mi17502_Dimitrije_Sekulic
  imports Main
begin

text\<open> 
  Zadatak 2, 1. dan: https://imomath.com/srb/zadaci/BIH_2013_bihmo_resenja.pdf

  2. Dat je niz sa a0 = 1, a1 = 1 i an+1 = 14*an - an-1 - 4 za prirodan broj n >= 1. 
     Pokazati da su svi članovi ovog niza potpuni kvadrati.

\<close>

(*Definišemo zdati niz*)

fun zadati_niz :: "nat \<Rightarrow> nat" where
"zadati_niz 0 = 1" |
"zadati_niz (Suc 0) = 1" |
"zadati_niz (Suc (Suc n)) =14 * zadati_niz (Suc n) - (zadati_niz n) - 4"

text\<open>
Prirodni broj koji je kvadrat drugog prirodnog broja naziva se potpuni kvadrat.
Odnosno, element a iz prstena A (ili skupa A na kojemu je definisana operacija množenja) 
potpuni je kvadrat ako je a=b^2 za neko b iz A.

https://hr.wikipedia.org/wiki/Potpuni_kvadrat
\<close>

definition potpuni :: "nat \<Rightarrow> bool" where
"potpuni n =  (\<exists>x\<le>n. n = x * x)"

thm "zadati_niz.simps"
thm "potpuni_def"

lemma resenje:
  fixes n :: nat
  shows "potpuni (zadati_niz n) = True"
  sorry
  

end