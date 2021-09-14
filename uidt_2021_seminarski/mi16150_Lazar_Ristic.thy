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


(* funkcija koja vraca a_n+i-ti element niza *)
fun a :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"a xs i n = xs ! (i-n-1)"

value "a [1::nat, 2, 3, 4, 5] 8 5 "
(*
a1=1, a2=2, a3=3, a4=4, a5=5, a6=1, a7=2, a8=3, a9=4, a10=5 ...
 *)

(* funkcija za odredjivanje sume niza koja je potrebna za dokaz *)
primrec suma_niza :: "nat list \<Rightarrow> nat" where
"suma_niza [] = 0" | 
"suma_niza (x#xs) = x + suma_niza xs"

(* provera za uslov a1 \<le> a2 ... \<le> an \<le> a1 + n *)
value "sorted ([1,2,3::nat] @ [(([1,2,3::nat] ! 1) + 3)])"

(* provera da je niz duzine n *)
fun niz_duzine_n :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
"niz_duzine_n A n = (if length A = n then True else False)"

lemma "zadatak":
  fixes n :: "nat" and A :: "nat list"  and a :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  assumes "sorted (A @ [((A ! 1) + n)])" 
  assumes "niz_duzine_n A n"
  assumes "\<forall>i \<ge> 1 . A ! (A ! i) \<le> n+i-1"
  shows "suma_niza A \<le> n*n"
proof (induction n)
  case 0
  then show ?case sorry
next
  case (Suc n)
  then show ?case sorry
qed
end