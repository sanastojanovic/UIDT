theory mi17042_Momir_Adzemovic
imports Main
begin

(* Prvi deo Seminarskog *)
(* Zadatak:
  Neka je n prirodan broj. Ako su a i b prirodni brojevi vecii od 1 takvi
  da je a*b= 2*n-1, dokazati da je broj ab-(a-b)-1 oblika k*2^(2m), gde
  je k neparan prirodan, a m prirodan broj. 
*)

theorem balkanska_matematicka_olimpijada_2001_prvi_zadatak:
  fixes n a c :: nat
  assumes "a > 1 \<and> b > 1 \<and> a*b = 2^n-1"
  (* Zbog simetricnost promenljivih a i b mozemo bez umanjenja opstosti
     da pretpostavimo sledece: "a \<ge> b" 
     Ova pretpostavka se uvodi zbog izraza a*b-(a-b)-1, jer
     u slucaju da je b > a vazi: "a-b = 0"
  *)
  assumes "a \<ge> b"
  shows "\<exists> k m ::nat . (odd k) \<and> (a*b-(a-b)-1 = k*2^m)"
  using assms
  sorry

(* Drugi Deo Seminarskog *)

end