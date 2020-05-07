(*  Naslov:      Seminariski prvi deo 
   Predmet:      Uvod u interaktivno dokazivanje teorema
   Student:      Filip Filipovic 
                 mi17113

link ka zadatku: https://imomath.com/srb/zadaci/2010_imac.pdf

The 4th International Mathematical Arhimede Competition
Bucharest 14. - 19. June 2010.
Seniorska liga
Prvi dan - 15. jun

Zadatak 1:
U ravni je dato 3n tacaka (n \<ge> 1), od kojih su svake tri nekolinearne.
Dokazati da postoji n medjusobno disjunktnih trouglova sa temenima 
u ovim tackama.

Koriscena literatura i spoljne veze:
1) Geometrija za informaticare, Tijana Sukilovic, Srdjan Vukmirovic
2) https://www.geeksforgeeks.org/check-if-two-given-line-segments-intersect/
3) https://kite.com/python/answers/how-to-determine-if-a-point-is-on-a-line-segment-in-python
4) http://poincare.matf.bg.ac.rs/~danijela/publications/ADG2012.pdf
5) https://easychair.org/publications/download/l91

*)

theory mi17113_Filip_Filipovic
  imports Complex_Main

begin

type_synonym tacka =  "real \<times> real"
type_synonym trougao = "tacka \<times> tacka \<times> tacka"

(*
Povrsina trougla odredjenog tackama 
A = (A_x, A_y) 
B = (B_x, B_y) 
C = (C_x, C_y)
se racuna kao
               |A_x  A_y  1|
P = 0.5 * abs (|B_x  B_y  1|)
               |C_x  C_y  1|
*)    
fun povrsina_trougla :: "tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> real" where 
  "povrsina_trougla (A_x, A_y) (B_x, B_y) (C_x, C_y) = 
    0.5 * abs (A_x*B_y+A_y*C_x+B_x*C_y-C_x*B_y-C_y*A_x-B_x*A_y)"


(*
Tacke A, B i C su kolinearne ako i samo ako one ne cine trougao, tj. ako
je trougao ABC degenerisan, tj. povrsine 0
*)
fun kolinearne :: "tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> bool" where
  "kolinearne A B C = (povrsina_trougla A B C = 0)"

fun sve_tacke_nekolinearne :: "tacka set \<Rightarrow> bool" where
  "sve_tacke_nekolinearne skup_tacaka = (\<forall> tacka1 tacka2 tacka3::tacka .
                                          (tacka1 \<in> skup_tacaka) \<and>
                                          (tacka2 \<in> skup_tacaka) \<and>
                                          (tacka3 \<in> skup_tacaka) \<and>
                                         -(kolinearne tacka1 tacka2 tacka3))"

(* Determinante orijentacije, za potrebe opcije 3 i 4 *)
fun znak :: "real \<Rightarrow> real" where
  "znak broj = (if broj < 0 then -1 else if broj = 0 then 0 else 1)"

fun determinanta_orijentacije :: "tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> real" where
  "determinanta_orijentacije (A_x, A_y) (B_x, B_y) (C_x, C_y) = 
                              ((B_x - A_x)*(C_y - A_y) - (C_x - A_x)*(B_y - A_y))"

fun determinanta_orijentacije2 :: "tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> real" where
  "determinanta_orijentacije2 (A_x, A_y) (B_x, B_y) (C_x, C_y) = 
                               ((B_y - A_y)*(C_x - B_x) - (B_x - A_x)*(C_y - B_y))"


(* OPCIJA 1 *)
fun da_li_su_tacke_jednake :: "tacka \<Rightarrow> tacka \<Rightarrow> bool" where
  "da_li_su_tacke_jednake (x1, y1) (x2, y2) = ((x1=x2) \<and> (y1=y2))" 


(* OPCIJA 2 *)


fun da_li_je_tacka_na_duzi :: "tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> bool" where
  "da_li_je_tacka_na_duzi (M_x, M_y) (A_x, A_y) (B_x, B_y) = 
                          ((kolinearne (M_x, M_y) (A_x, A_y) (B_x, B_y)) \<and>
                           (M_x <= (max A_x B_x)) \<and> 
                           (M_x >= (min A_x B_x)) \<and>     
                           (M_y <= (max A_y B_y)) \<and> 
                           (M_y >= (min A_y B_y)))"

(* OPCIJA 3 *)

(*vise o ovome: https://www.geeksforgeeks.org/check-if-two-given-line-segments-intersect/*)
fun da_li_se_duzi_seku_ili_poklapaju_preko_orijentacija :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> bool" where
  "da_li_se_duzi_seku_ili_poklapaju_preko_orijentacija o1 o2 o3 o4 A B C D = 
  (((o1 \<noteq> o2) \<and> (o3 \<noteq> o4)) \<or>
   ((o1 = 0) \<and> (da_li_je_tacka_na_duzi C A B)) \<or>
   ((o2 = 0) \<and> (da_li_je_tacka_na_duzi D A B)) \<or>
   ((o3 = 0) \<and> (da_li_je_tacka_na_duzi A C D)) \<or>
   ((o4 = 0) \<and> (da_li_je_tacka_na_duzi B C D)))"

fun da_li_se_duzi_seku_ili_poklapaju :: "tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> bool" where
  "da_li_se_duzi_seku_ili_poklapaju A B C D = 
(da_li_se_duzi_seku_ili_poklapaju_preko_orijentacija 
  (znak (determinanta_orijentacije2 A B C)) 
  (znak (determinanta_orijentacije2 A B D)) 
  (znak (determinanta_orijentacije2 C D A)) 
  (znak (determinanta_orijentacije2 C D B)) 
  A 
  B 
  C 
  D)"



(* OPCIJA 4 *)

(*
Tacka P pripada trouglu ABC ako i samo ako su svi trouglovi ABP, BCP i CAP iste 
orijentacije, tj ako i samo ako: sign(D ABP) = sign(D BCP) = sign(D CAP), gde je D
determinanta_orijentacije, definisana kao u funkciji iznad (posledica vektorskog proizvoda).
*)
fun tacka_pripada_unutrasnjosti_trougla :: "tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> bool" where
  "tacka_pripada_unutrasnjosti_trougla P A B C = ( (znak (determinanta_orijentacije A B P)
                                                   =znak (determinanta_orijentacije B C P)) \<and>
                                                   (znak (determinanta_orijentacije B C P)
                                                   =znak (determinanta_orijentacije C A P)) \<and>
                                                   (znak (determinanta_orijentacije A B P)
                                                   =znak (determinanta_orijentacije C A P)) )"




(*
Trouglovi su disjunktni ako nemaju ni jednu zajednicku tacku
Posmatrajmo suprotan dogadjaj. Kada trouglovi imaju barem jednu, zajednicku
tacku, tj kada se dva trougla u ravni "seku".

opcija 1:  Trouglovi mogu da se "dodiruju" samo u jednoj tacki, na
           nacin da imaju samo jedno zajednicko teme, i to proveravamo funkcijom 
           da_li_su_tacke_jednake.

opcija 2: Teme prvog trougla moze da lezi na jednoj stranici drugog i to proveravamo
          funkcijom da_li_je_tacka_na_duzi

opcija 3: Neke stranice ovih trouglova se ili seku ili delimicno poklapaju ili u potpunosti
          poklapaju i to proveravamo funkcijom da_li_se_duzi_seku_ili_poklapaju
          vise o ovome: https://www.geeksforgeeks.org/check-if-two-given-line-segments-intersect/

opcija 4: Barem jedno teme prvog trougla se nalazi u unutrasnjosti drugog i to proveravamo
          funkcijom tacka_pripada_unutrasnjosti_trougla

*)
fun da_li_se_trouglovi_seku :: "tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> bool" where
  "da_li_se_trouglovi_seku t1 t2 t3 t4 t5 t6 = ( 
                                    (da_li_su_tacke_jednake t1 t4) \<or>
                                    (da_li_su_tacke_jednake t1 t5) \<or>
                                    (da_li_su_tacke_jednake t1 t6) \<or>
                                    (da_li_su_tacke_jednake t2 t4) \<or>
                                    (da_li_su_tacke_jednake t2 t5) \<or>
                                    (da_li_su_tacke_jednake t2 t6) \<or>
                                    (da_li_su_tacke_jednake t3 t4) \<or>
                                    (da_li_su_tacke_jednake t3 t5) \<or>
                                    (da_li_su_tacke_jednake t3 t6) \<or>

                                    (da_li_je_tacka_na_duzi t1 t4 t5) \<or>
                                    (da_li_je_tacka_na_duzi t1 t5 t6) \<or>
                                    (da_li_je_tacka_na_duzi t1 t6 t4) \<or>
                                    (da_li_je_tacka_na_duzi t2 t4 t5) \<or>
                                    (da_li_je_tacka_na_duzi t2 t5 t6) \<or>
                                    (da_li_je_tacka_na_duzi t2 t6 t4) \<or>
                                    (da_li_je_tacka_na_duzi t3 t4 t5) \<or>
                                    (da_li_je_tacka_na_duzi t3 t5 t6) \<or>
                                    (da_li_je_tacka_na_duzi t3 t6 t4) \<or>

                                    (da_li_se_duzi_seku_ili_poklapaju t1 t2 t4 t5) \<or>
                                    (da_li_se_duzi_seku_ili_poklapaju t1 t2 t5 t6) \<or>
                                    (da_li_se_duzi_seku_ili_poklapaju t1 t2 t6 t4) \<or>
                                    (da_li_se_duzi_seku_ili_poklapaju t2 t3 t4 t5) \<or>
                                    (da_li_se_duzi_seku_ili_poklapaju t2 t2 t5 t6) \<or>
                                    (da_li_se_duzi_seku_ili_poklapaju t2 t3 t6 t4) \<or>
                                    (da_li_se_duzi_seku_ili_poklapaju t3 t1 t4 t5) \<or>
                                    (da_li_se_duzi_seku_ili_poklapaju t3 t1 t5 t6) \<or>
                                    (da_li_se_duzi_seku_ili_poklapaju t3 t1 t6 t4) \<or>

                                    (tacka_pripada_unutrasnjosti_trougla t1 t4 t5 t6) \<or>
                                    (tacka_pripada_unutrasnjosti_trougla t2 t4 t5 t6) \<or>
                                    (tacka_pripada_unutrasnjosti_trougla t3 t4 t5 t6) \<or>
                                    (tacka_pripada_unutrasnjosti_trougla t4 t1 t2 t3) \<or>
                                    (tacka_pripada_unutrasnjosti_trougla t5 t1 t2 t3) \<or>
                                    (tacka_pripada_unutrasnjosti_trougla t6 t1 t2 t3))"

fun disjunktni :: "tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> tacka \<Rightarrow> bool" where
  "disjunktni t1 t2 t3 t4 t5 t6 =  -(da_li_se_trouglovi_seku t1 t2 t3 t4 t5 t6)"

fun disjunktni_za_trouglove :: "trougao \<Rightarrow> trougao \<Rightarrow> bool" where
  "disjunktni_za_trouglove (t1, t2, t3) (t4, t5, t6) = disjunktni t1 t2 t3 t4 t5 t6"

fun trougao_pripada_skupu_tacaka :: "trougao \<Rightarrow> tacka set \<Rightarrow> bool" where
  "trougao_pripada_skupu_tacaka (t1, t2, t3) skup_tacaka = 
                                ((t1 \<in> skup_tacaka) \<and> (t2 \<in> skup_tacaka) \<and> (t3 \<in> skup_tacaka))"

(* Glavno tvrdjenje *)
lemma
  fixes skup_tacaka :: "tacka set"
  assumes "skup_tacaka \<noteq> {}"
  assumes "(card skup_tacaka) mod 3 = 0"  
  assumes "\<forall> tacka1 tacka2 tacka3 . (tacka1 \<in> skup_tacaka) \<and> 
                                    (tacka2 \<in> skup_tacaka) \<and> 
                                    (tacka3 \<in> skup_tacaka) --> 
                                   -(kolinearne tacka1 tacka2 tacka3)"
  fixes skup_trouglova :: "trougao set"
  assumes "skup_trouglova \<noteq> {}"
  assumes "card skup_trouglova = (card skup_tacaka) div 3"  
  assumes "\<forall> trougao . (trougao \<in> skup_trouglova) \<longrightarrow>
                       (trougao_pripada_skupu_tacaka trougao skup_tacaka)"
  fixes trougao1 trougao2 :: "trougao"
  shows " 
                            ( \<forall> trougao1 trougao2 . 
                            (trougao1 \<in> skup_trouglova) \<and> 
                            (trougao2 \<in> skup_trouglova) \<longrightarrow>
                            (disjunktni_za_trouglove trougao1 trougao2))"
  using assms
  (* sledgehammer *)   (*Nazalost, lema je suvise slozena za auto i sledgehammer *)
  (* by auto *)
  sorry

end