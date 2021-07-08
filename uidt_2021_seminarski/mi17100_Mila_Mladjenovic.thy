theory mi17100_Mila_Mladjenovic
imports Complex_Main

begin
text‹
  https://www.imo-official.org/problems/IMO2018SL.pdf
  Zadatak: Algebra A2
  Tekst zadatka: Pronaci sve pozitivne cele brojeve n ≥ 3 za koje postoje
  realni brojevi a1, a2, ..., an, a_n+1 a1, a_n+2 = a2 takvi da
            a_i*a_i+1 + 1 = a_i+2
  za svako i = 1, 2, ..., n.
›

type_synonym sekvenca = "real list"

primrec indeks_lista :: "sekvenca ⇒ real ⇒ nat ⇒ nat" where
"indeks_lista [] _ brojac = 0"|
"indeks_lista (x # xs) a brojac = (if (x = a) then brojac
                                  else (indeks_lista xs a (brojac+1)))"

value "indeks_lista [1,2,3,4,5,13,15::real] 2 0"

(*                      lista sa el. ⇒ x1 ⇒ x2 x x3     *)
fun vrati_tri_broja :: "sekvenca ⇒ real ⇒ real×real" where
"vrati_tri_broja xs x1 =
(let i1 = indeks_lista xs x1 0; n = (size xs) in
(if (n - i1 + 1 > 3) then (xs ! (i1 + 1), xs ! (i1 + 2))
else if (i1 + 1 = n-1) then (xs ! (n - 1), xs ! 0)
else (xs ! 0, xs ! 1)))"

value "indeks_lista [1::real,2,3,4,5] 4 0" (*vraca index od elemnta u listi*)
value "size [1::real,2,3,4,5]" (*n*)
value "vrati_tri_broja [1,2,3,4,5] 4" (*vraca dva broja iz sekvence nakon broja 4*)

(*Da vazi da je a_i * a_i+1 + 1 = a_i+2*)
fun izraz_uslov :: "real ⇒ real ⇒ real ⇒ bool" where
"izraz_uslov a b c = (if (a*b + 1 = c) then True else False)"

(*Da uslov a_i * a_i+1 + 1 = a_i+2 vazi za -dat-i element liste*)
fun ispunjava_uslov :: "sekvenca ⇒ real ⇒ bool" where
"ispunjava_uslov xs x =
 izraz_uslov x (fst (vrati_tri_broja xs x)) (snd (vrati_tri_broja xs x))"

value "ispunjava_uslov [-1, -1, 2] 2" (*True*)
value "ispunjava_uslov [-1, 1, 2] 2" (*False*)

(*Da uslov a_i * a_i+1 + 1 = a_i+2 vazi za -svaki- element liste*)
fun uslov:: "sekvenca ⇒ bool" where
"uslov [] = False"|
"uslov xs = (if (size xs)<3 then False
             else if (∀ x ∈ set xs. ispunjava_uslov xs x) then True
             else False)"

value "uslov [-1,-1,2]" (*True*)
value "uslov [-1,1,2]" (*False*)

(*Vidimo da je [-1,-1,2] jedno resenje. Dokazacemo da svaki pozitivan element prate
 dva negativna, a nakon njih opet ide pozitivna vrednost.
 Odavde ce slediti da je n deljivo sa tri.*)

(*------------------------------------------------------------------------------------------------*)

(*Ako u sekvenci imamo dva pozitivna uzastopna broja a_i i a_i+1, onda ce a_i+2 biti
 a_i+2 =  a_i*a_i+1 + 1 > 1, tako da je i a_i+2 pozitivno. Iz ovoga indukcijom vidimo da su svi 
brojevi u sekvenci veci od 1, pa samim tim i pozitivni. Odavde ce da sledi da su svi brojevi
u sekvenci pozitivni (i veci od 1), ali onda je  a_i+2 =  a_i* a_i+1 + 1 ≥ 1 * a_i+1 + 1 > a_i+1 ∀i
sto je ne moguce jer je nasa sekvenca periodicna i ne moze da raste sa svakim novim elementom.*) 

lemma "svi_pozitivni_u_sekvenci":
  assumes "(a1::real)>0"
  assumes "(a2::real)>0"
  assumes "a1 = a2*a3 + 1"
  assumes "a2 = a3*a1 + 1"
  assumes "a3 = a1*a2 + 1"
  shows "a3 > 1 ∧ a1 > 1 ∧ a2 > 1"
proof -
  from assms(1) and assms(2) have "a1*a2>0" by auto
  from this and assms(5) have "a3 > 1" by auto
  from this and assms(2) have "a2*a3>0" by auto
  from this and assms(3) have "a1 > 1" by auto
  from this and ‹a3 > 1› have "a3*a1>0" by auto
  from this and assms(4) have "a2 > 1" by auto
  from this and ‹a1 > 1› and ‹a3 > 1› show "a3 > 1 ∧ a1 > 1 ∧ a2 > 1" by auto
qed

lemma "kontradikcija_svi_pozitivni_u_sekvenci":
  assumes "(a1::real)>1"
  assumes "(a2::real)>1"
  assumes "a3 = a1*a2 + 1"
  shows "a3>a2"
proof -
  from assms(1) and assms(2) have "a1*a2 > 0" by auto
  from this have "a1*a2 + 1 > 1" by auto
  from assms(1) and assms(2) have "a1*a2 ≥ 1*a2" by auto
  from this have "a1*a2 + 1 ≥ 1*a2 + 1" by auto
  from this and assms(3) have "a3  ≥ 1*a2 + 1" by auto
  from this and assms(2) have "1*a2 + 1 > a2" by auto
  from this and ‹a3 ≥ 1*a2 + 1› show "a3 > a2" by auto
qed

(*Ako je 0 u nasoj sekvenci, npr. a_i = 0 (za neki indeks i) imacemo:
a_i+1 = a_i-1*a_i + 1 > 0
a_i+2 = a_i*a_i+1 + 1 > 0
ovo su dva pozitivna i uzastopna elementa pa dobijamo istu kontradikciju kao i malo pre.*)

lemma "nula_u_sekvenci1":
  assumes "(a1::real) = 0"
  assumes "(a2::real) = (a0::real)*a1 + 1"
  shows "a2>0"
proof -
  from assms have "a0 * a1 = 0" by auto
  from this have "a0*a1 + 1 = 1" by auto
  from this and assms(2) show "a2>0" by auto
qed

lemma "nula_u_sekvenci2":
  assumes "(a1::real) = 0"
  assumes "(a3::real) = a1*(a2::real) + 1"
  shows "a3>0"
proof -
  from assms have "a1 * a2 = 0" by auto
  from this have "a1*a2 + 1 = 1" by auto
  from this and assms(2) show "a3>0" by auto
qed

(*Ako je a_i<0 i  a_i+1<0 onda je  a_i+2 =  a_i* a_i+1 + 1 > 1, tj. a_i+2 je pozitivno (a_i+2>0).
Stoga imamo da nakon dva negativna broja ide jedan pozitivan.*)

lemma "dva_negativna_pa_pozitivan":
  assumes "(a1::real) < 0"
  assumes "(a2::real) < 0"
  assumes "a3 = a1*a2 + 1"
  shows "a3 > 0"
proof -
  from assms(1) and assms(2) have "a1*a2 > 0" by (simp add: mult_neg_neg)
  from this and assms(3) show "a3 > 0" by auto
qed

(*Slucaj kada se pozitivni i negativni brojevi smenjuju,
 npr.  a_i<0 ,  a_i+1>0,  a_i+2<0,  a_i+3>0 ...
odatle sledi:  a_i* a_i+1 + 1 =  a_i+2 < 0 <  a_i+3 =  a_i+1* a_i+2 + 1
zakljucujemo da je  a_i <  a_i+2 
Stoga, negativni brojevi prave rastucu subsekvencu:  a_i <  a_i+2 <  a_i+4 < ...
sto nije moguce jer je sekvenca periodicna.*)

lemma "neizmenicno_poz_neg":
  assumes "(a1::real)<0"   (*1*)
  assumes "(a2::real)>0"   (*2*)
  assumes "(a3::real)<0"   (*3*)
  assumes "(a4::real)>0"   (*4*)
  assumes "(a5::real)<0"   (*5*)
  assumes "(a6::real)>0"   (*6*)
  assumes "a3 = a1*a2 + 1" (*7*)
  assumes "a4 = a2*a3 + 1" (*8*)
  assumes "a5 = a3*a4 + 1" (*9*)
  assumes "a6 = a4*a5 + 1" (*10*)
  shows "a1 < a3 ∧ a3 < a5"
proof -
  from assms(3) and assms(7) have "a1 * a2 + 1 < 0" by auto
  from assms(4) and assms(8) have "a2 * a3 + 1 > 0" by auto
  from this and ‹a1 * a2 + 1 < 0› have "a1 * a2 + 1 < a2 * a3 + 1" by auto
  from this have "a1 * a2 < a2 * a3" by auto
  from this and assms(2) have "a1 < a3" by auto
  from assms(5) and assms(9) have " a3 * a4 + 1 < 0" by auto
  from assms(6) and assms(10) have " a4 * a5 + 1 > 0" by auto
  from this and ‹a3 * a4 + 1 < 0› have "a3 * a4 + 1 < a4 * a5 + 1" by auto
  from this have "a3 * a4 < a4 * a5" by auto
  from this and assms(4) have "a3 < a5" by auto
  from this and ‹a1 < a3› show "a1 < a3 ∧ a3 < a5" by auto
qed

(*Jedini slucaj koji je ostao jeste da imamo uzastopne negativne broje. Pretpostavicemo
da je  a_i<0 i  a_i+1<0, onda imamo da je  a_i+2 =  a_i* a_i+1 + 1 > 1. Broj  a_i+3 mora
biti negativan, pokazacemo da a_i+4 mora da bude negativno.
 a_i+3<0
 a_i+4 =  a_i+2 * a_i+3 + 1 < 1 <  a_i * a_i+1 + 1 =  a_i+2 odatle imamo
 a_i+5 -  a_i+4 = ( a_i+3 * a_i+4 + 1) - ( a_i+2 * a_i+3 + 1) =  a_i+3 * (a_i+4 -  a_i+2) > 0
 odatle  je a_i+5 > a_i+4. Posto makar jedan od  a_i+4 i  a_i+5 mora biti pozitivan broj,
to znaci da je  a_i+4 negativno. *)

lemma "uzastopni_negativni":
  assumes "(a1::real)<0"           (*1*)
  assumes "(a2::real)<0"           (*2*)
  assumes "(a3::real) = a1*a2 + 1" (*3*)
  assumes "(a4::real)<0"           (*4*)
  assumes "(a4::real) = a2*a3 + 1" (*5*)
  assumes "(a5::real) = a3*a4 + 1" (*6*)
  assumes "(a6::real) = a4*a5 + 1" (*7*)
  assumes "a6<0 ∨ a5<0"            (*8*)
  shows "a5<0"
proof -
  from assms(1) and assms(2) have "a1 * a2 + 1 > 1" by (simp add: mult_neg_neg)
  from this and assms(3) have "a3 > 1" by auto (*a3 > 1*)
  from assms(4) and assms(5) have "a2 * a3 + 1 < 0" by auto
  from assms(4) and ‹a3 > 1› have "a3 * a4 < 0" by (metis assms(1) assms(2) assms(3) dva_negativna_pa_pozitivan mult_pos_neg)
  from this have "a3 * a4 + 1 < 1" by auto (*a5 < 1*)
  from this and ‹a3 > 1› and assms(6) have "a5 - a3 < 0" by auto
  from assms(6) and assms(7) have "a6 - a5 = (a4*a5 + 1) - (a3*a4 + 1)" by auto
  have "... = a4*a5 - a3*a4" by auto
  have "... = a4 * (a5 - a3)" by (simp add: right_diff_distrib)
  from this and ‹a5 - a3 < 0› and assms(4) and assms(6) and assms(7) have "a6 - a5 > 0" by (simp add: zero_less_mult_iff)
  from this have "a6 > a5" by auto
  from this and assms(8) show "a5<0"by auto
qed

(*Sada  a_i+3 i  a_i+4 su negativni, a  a_i+5 je pozitivno. Dakle nakon dva negativna ide pozitivan broj
i taj sablon se ponjava. Broj n je bilo koji broj koji je deljiv sa 3. To je resenje.*)

end
