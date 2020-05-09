theory mi17113_Filip_Filipovic_2
  imports Complex_Main "HOL-Computational_Algebra.Polynomial" 
  
begin
type_synonym  polinom = "real list"

fun vrednost_polinoma :: "polinom \<Rightarrow> real \<Rightarrow> real" where
  "vrednost_polinoma P x = foldl (\<lambda> acc (koef, st). acc + koef * x ^ st) (0::real) (zip P [0..<length P])"

definition P1 :: "real list" where
  "P1 = [1, 2, -1, 6, 6, 6, 6, 4]"

value "vrednost_polinoma P1 100 = (poly (poly_of_list P1)) 100"

text \<open>Alternativne definicije\<close>

fun vrednost_polinoma' :: "polinom \<Rightarrow> real \<Rightarrow> real" where
  "vrednost_polinoma' P x = sum_list (map2 (*) P (map (\<lambda> s. x^s) [0..<length P]))"

value "vrednost_polinoma' P1 100 = (poly (poly_of_list P1)) 100"

fun vrednost_polinoma_horner :: "polinom \<Rightarrow> real \<Rightarrow> real" where
  "vrednost_polinoma_horner P x = foldl (\<lambda> acc Pi. acc*x + Pi) 0 (rev P)"

value "vrednost_polinoma_horner P1 100 = (poly (poly_of_list P1)) 100"



fun podeli_polinom_konstantom :: "real poly \<Rightarrow> real \<Rightarrow> real poly" where
  "podeli_polinom_konstantom polinom konstanta = map_poly (\<lambda> koef. koef / konstanta) polinom"

term "podeli_polinom_konstantom [:1,2,3:] 3.14"

definition lagranz_koefs :: "(real\<times>real) set \<Rightarrow> real poly" where
  "lagranz_koefs xy_skup = 
  (\<Sum>(xs, ys)\<in>xy_skup.
      [:ys:] *
      (\<Prod>(xp, yp)\<in>xy_skup.
         if xs = xp then [:1:]
         else podeli_polinom_konstantom [:- xp, 1:] (xs - xp)))" 


thm lagranz_koefs_def
definition lagranz :: "real list \<Rightarrow> real list \<Rightarrow> real \<Rightarrow> real" where
  "lagranz X Y tacka_x = poly (lagranz_koefs (set (zip X Y))) tacka_x"


value "lagranz [1.0000::real,1.1000,1.2000,1.3000,1.4000,1.5000] [1.7183::real,1.7942,1.8801,1.9793,2.0952,2.2317] (1.430::real)" (* ocekivani izlaz: 2.1338 ili u isabellu 42675791237 / 20000000000 *)

(* Za Lagranza bi mozda moglo da se dokaze da ako x \<in> X i y \<in> Y i ako su svi x-ovi razliciti, da je
   tada lagranz X Y x = y *)
term "map "
value "map fst [(1,2),(3::nat,4::nat)]"
lemma
  fixes x::real and y::real
  fixes xy_lista::"(real\<times>real) list"
  assumes "xy_lista \<noteq> []"
  assumes "(x,y) \<in> set xy_lista"
  assumes "distinct (map fst xy_lista) = True"
  shows "lagranz (map fst xy_lista) (map snd xy_lista) x = y"
  proof (induction xy_lista)
    case Nil
    then show ?case
      using assms
      sorry
  next
    case (Cons l0 l)
    have "lagranz (map fst (l0 # l)) (map snd (l0 # l)) x = lagranz (fst l0 # map fst l) (snd l0 # map snd l) x"
      by simp
    
    then show ?case sorry
  qed


(*
fun podeljene_razlike :: "(real\<times>real) list \<Rightarrow> real" where
  "podeljene_razlike l = (if length l = 0
                            then
                              -1 
                          else if length l = 1
                            then 
                              snd (hd l) 
                          else 
                              ((podeljene_razlike (tl l))-(podeljene_razlike (butlast l)))/((fst (last l)) - fst(hd l))
                          )"*)

fun podeljene_razlike :: "(real\<times>real) list \<Rightarrow> real" where
  "podeljene_razlike [] = 0"
| "podeljene_razlike [(x, y)] = y"
| "podeljene_razlike l = 
          (podeljene_razlike (tl l)-podeljene_razlike (butlast l)) /
          (fst (last l) - fst (hd l))"

(* Testiranje *)
value "podeljene_razlike [(1, 2), (3, 4), (5, 8)]"
value "podeljene_razlike [(1, 2), (3, 4), (5, 8), (6, 7)]"

(*
Posto se ovaj izraz ponavlja na vise mesta, mozda bi imalo smisla izdvojiti ga u posebnu funckiju.
Takodje, mozda bi umesto vrednosti xs bolje bilo slati indeks s (tada ne bi bila bitna ona pretpostavka
da su svi x-ovi razliciti).
*)

fun pom :: "real \<Rightarrow> real \<Rightarrow> real" where
  "pom xs xp = (if xp = xs then 1 else xs - xp)"


definition podeljene_razlike2_proizvod :: "real \<Rightarrow> (real \<times> real) list \<Rightarrow> real" where
  "podeljene_razlike2_proizvod xs l = (\<Prod>(xp, yp) \<leftarrow> l. pom xs xp)"

lemma proizvod_poslednji:
  fixes l::"real list"
  assumes "l \<noteq> []"
  shows "(\<Prod> x \<leftarrow> l . f x) = (\<Prod> x \<leftarrow> butlast l . f x) * f (last l)"
  by (smt append_butlast_last_id assms list.simps(8) list.simps(9) map_append mult.right_neutral prod_list.Cons prod_list.Nil prod_list.append)

lemma podeljene_razlike2_proizvod_butlast: 
  fixes l::"(real\<times>real) list" and xs::real
  assumes "length l > 1" "distinct (map fst l)"
  shows "podeljene_razlike2_proizvod xs l = (let (xp, yp) = last l
    in podeljene_razlike2_proizvod xs (butlast l) * pom xs xp)"
  unfolding podeljene_razlike2_proizvod_def
  by (smt append_Nil2 append_butlast_last_id assms(1) case_prod_beta' gr_implies_not_zero length_0_conv list.simps(9) map_append mult.left_commute prod_list.Cons prod_list.append semiring_normalization_rules(7))

lemma podeljene_razlike2_proizvod_butlast_bez_let: 
  fixes l::"(real\<times>real) list" and xs::real
  assumes "length l > 1" "distinct (map fst l)"
  shows "podeljene_razlike2_proizvod xs l = podeljene_razlike2_proizvod xs (butlast l) * pom xs (fst (last l))"
  unfolding podeljene_razlike2_proizvod_def
  by (metis assms(1) assms(2) case_prod_beta' podeljene_razlike2_proizvod_butlast podeljene_razlike2_proizvod_def)


definition podeljene_razlike2 :: "(real\<times>real) list \<Rightarrow> real" where
  "podeljene_razlike2 l =
   (\<Sum>(xs, ys) \<leftarrow> l. ys / podeljene_razlike2_proizvod xs l)"

(* Testiranje *)
value "podeljene_razlike2 [(1, 2), (3, 4), (5, 8)]"
value "podeljene_razlike2 [(1, 2), (3, 4), (5, 8), (6, 7)]"

lemma sabiranje_poslednji:
  fixes l :: "real list"
  assumes "l \<noteq> []"
  shows "(\<Sum> x \<leftarrow> l. f x) = (\<Sum> x \<leftarrow> (butlast l). f x) + f (last l)"
  by (metis (mono_tags, hide_lams) Nil_is_map_conv add.right_neutral append_butlast_last_id assms last_map map_butlast sum_list.Cons sum_list.Nil sum_list.append)

fun podeljene_razlike2_poslednji_sabirak :: "(real \<times> real) list \<Rightarrow> real" where
  "podeljene_razlike2_poslednji_sabirak l = 
    (let (xs, ys) = last l
      in  ys /podeljene_razlike2_proizvod xs l)"

definition podeljene_razlike2_bez_poslednjeg_sabirka :: "(real \<times> real) list \<Rightarrow> real" where
  "podeljene_razlike2_bez_poslednjeg_sabirka l = 
     (\<Sum>(xs, ys) \<leftarrow> butlast l. ys / podeljene_razlike2_proizvod xs l)"

definition podeljene_razlike2_bez_nultog_sabirka :: "(real \<times> real) list \<Rightarrow> real" where
  "podeljene_razlike2_bez_nultog_sabirka l = 
     (\<Sum>(xs, ys) \<leftarrow> tl l. ys / podeljene_razlike2_proizvod xs l)"

fun podeljene_razlike2_nulti_sabirak :: "(real \<times> real) list \<Rightarrow> real" where
  "podeljene_razlike2_nulti_sabirak l = 
     (let (xs, ys) = hd l
       in  ys / podeljene_razlike2_proizvod xs l)"

lemma podeljene_razlike2_izvlacenje_n_tog_sabirka_sume:
  fixes l :: "(real\<times>real) list" 
  assumes "l \<noteq> []"
  shows "podeljene_razlike2 l = podeljene_razlike2_bez_poslednjeg_sabirka l + podeljene_razlike2_poslednji_sabirak l"
  sorry
  (*by (smt append_butlast_last_id list.map(2) list.simps(8) map_append sum_list.Cons sum_list.Nil sum_list.append)*)

lemma podeljene_razlike2_izvlacenje_0_tog_sabirka_sume:
  fixes l :: "(real\<times>real) list"
  assumes "l \<noteq> []"
  shows "podeljene_razlike2 l = podeljene_razlike2_bez_nultog_sabirka l + podeljene_razlike2_nulti_sabirak l"
  proof-
    have "(\<Sum>(ra, r)\<leftarrow>l. r / podeljene_razlike2_proizvod ra l) = (\<Sum>(ra, r)\<leftarrow>hd l # tl l. r / podeljene_razlike2_proizvod ra l)"
      by (simp add: assms)
    then show ?thesis
      by (simp add: podeljene_razlike2_bez_nultog_sabirka_def podeljene_razlike2_def)
  qed



lemma glava_nije_rep_za_barem_2_interpolaciona_cvora:
  fixes l :: "(real \<times> real) list"
  assumes "length l > 1" "distinct (map fst l) = True"
  shows "fst (last l) - fst (hd l)  \<noteq> 0"
proof-
  have "last (map fst l) \<noteq> hd (map fst l)"
    using assms
    by (metis diff_less hd_conv_nth last_conv_nth length_greater_0_conv length_map list.size(3) not_one_less_zero nth_eq_iff_index_eq zero_less_diff zero_less_one)
  then have "last l \<noteq> hd l"
    using assms 
    by (metis gr_implies_not_zero hd_map last_map length_0_conv)
  then have "fst (last l) \<noteq> fst (hd l)"
    using assms
    by (metis \<open>last (map fst l) \<noteq> hd (map fst l)\<close> last_map list.map_sel(1) list.size(3) not_less_zero)
  then show ?thesis
    by simp
qed

(* Pomocno izracunavanje1 *)
fun podeljene_razlike2_pomocno_izracunavanje1_definicija1 :: "(real \<times> real) list \<Rightarrow> real" where 
  "podeljene_razlike2_pomocno_izracunavanje1_definicija1 l =  
    (\<Sum>(xs, ys) \<leftarrow> [hd l]. ys / (\<Prod>(xp, yp) \<leftarrow> l. pom xs xp))"

fun podeljene_razlike2_pomocno_izracunavanje1_definicija2 :: "(real \<times> real) list \<Rightarrow> real" where 
  "podeljene_razlike2_pomocno_izracunavanje1_definicija2 l =  
    (let (xs,ys) = hd l 
      in (ys /podeljene_razlike2_proizvod xs l))"

value "podeljene_razlike2_pomocno_izracunavanje1_definicija1 [(1,2),(3::real,4::real)]"
value "podeljene_razlike2_pomocno_izracunavanje1_definicija2 [(1,2),(3::real,4::real)]"


value "(let (xs,ys) = hd [(1::real, 2::real), (3, 4), (5, 8)] 
                       in (let (xp, yp) = last [(1::real, 2::real), (3, 4), (5, 8)] 
                                  in  ys/((podeljene_razlike2_proizvod xs (butlast [(1::real, 2::real), (3, 4), (5, 8)] )) * pom xs xp)))"

value "(let (xs,ys) = hd [(1::real, 2::real), (3, 4), (5, 8)] 
                       in ys / (let (xp, yp) = last [(1::real, 2::real), (3, 4), (5, 8)]
    in podeljene_razlike2_proizvod xs (butlast [(1::real, 2::real), (3, 4), (5, 8)]) * pom xs xp))"

lemma podeljene_razlike2_pomocno_izracunavanje1_lema1:
  fixes l::"(real\<times>real) list"
  assumes "length l > 1" "distinct (map fst l)"
  shows "podeljene_razlike2_pomocno_izracunavanje1_definicija2 l = podeljene_razlike2_nulti_sabirak l"
  proof (induction l rule: podeljene_razlike2_pomocno_izracunavanje1_definicija2.induct)
    case (1 l)
    have "podeljene_razlike2_pomocno_izracunavanje1_definicija2 l  = (let (xs,ys) = hd l 
                       in ys / podeljene_razlike2_proizvod xs l)"
      by simp
    also have "... = (let (xs,ys) = hd l 
                       in  ys / podeljene_razlike2_proizvod xs l)"
      unfolding podeljene_razlike2_proizvod_def
      by simp
    also have "... = podeljene_razlike2_nulti_sabirak l"
      by simp
    then show ?case 
      by simp 
  qed 

lemma pom_lema1:
  fixes l::"(real\<times>real) list"
  assumes "length l > 1" "distinct (map fst l)"
  shows "pom (fst (hd l)) (fst (last l)) = fst (hd l) - fst (last l)"
  using assms(1) assms(2) glava_nije_rep_za_barem_2_interpolaciona_cvora 
  by auto

lemma pom_lema2:
  fixes l::"(real\<times>real) list"
  assumes "length l > 1" "distinct (map fst l)"
  shows "hd (butlast l) = hd l"
  by (metis assms(1) gr_implies_not_zero hd_conv_nth length_0_conv length_butlast nth_butlast zero_less_diff)

lemma podeljene_razlike2_pomocno_izracunavanje1_lema2:
  fixes l::"(real\<times>real) list"
  assumes "length l > 1" "distinct (map fst l)"
  shows "(podeljene_razlike2_nulti_sabirak (butlast l))/(fst (hd l) - fst (last l))  = podeljene_razlike2_nulti_sabirak l"
proof (induction l rule: podeljene_razlike2_nulti_sabirak.induct)
  case (1 l)
  have "(podeljene_razlike2_nulti_sabirak (butlast l))/(fst (hd l) - fst (last l)) = 
          (let (xs, ys) = hd (butlast l)
            in  ys / podeljene_razlike2_proizvod xs (butlast l))/(fst (hd l) - fst (last l))"
    by simp
  also have "... = 
          (let (xs, ys) = hd (butlast l)
            in  (ys / podeljene_razlike2_proizvod xs (butlast l))/(fst (hd l) - fst (last l)))"
    by (simp add: case_prod_beta)
  also have "... = 
          (let (xs, ys) = hd (butlast l)
            in  ys / ((fst (hd l) - fst (last l))*podeljene_razlike2_proizvod xs (butlast l)))"
    by (simp add: case_prod_beta)
  also have "... = 
          (let (xs, ys) = hd (butlast l)
            in  ys / ((fst (hd l) - fst (last l)) * (\<Prod>(xp, yp) \<leftarrow> (butlast l). pom xs xp)))"
    using podeljene_razlike2_proizvod_def 
    by simp
  also have "... = 
          (let (xs, ys) = hd (butlast l)
            in  ys / ((pom (fst (hd l)) (fst (last l))) * (\<Prod>(xp, yp) \<leftarrow> (butlast l). pom xs xp)))"
    using assms
    using pom_lema1
    (* by auto *) (* Zasto ne radi? Da li mu smeta razlika izmedju plavog l, ?l i narandzastog l? *) 
    sorry
  also have "... = 
          (let (xs, ys) = hd (butlast l)
            in  ys / ((pom xs (fst (last l))) * (\<Prod>(xp, yp) \<leftarrow> (butlast l). pom xs xp)))"
    by (smt \<open>(let (xs, ys) = hd (butlast l) in ys / ((fst (hd l) - fst (last l)) * (\<Prod>(xp, yp)\<leftarrow>butlast l. pom xs xp))) = (let (xs, ys) = hd (butlast l) in ys / (pom (fst (hd l)) (fst (last l)) * (\<Prod>(xp, yp)\<leftarrow>butlast l. pom xs xp)))\<close> butlast.simps(1) butlast.simps(2) case_prod_beta divide_cancel_left hd_Cons_tl hd_conv_nth last_conv_nth length_butlast list.sel(1) list.simps(8) list.size(3) mult_cancel_left1 pom.simps prod_list.Nil)
  also have "... = 
          (let (xs, ys) = hd (butlast l)
            in  ys / ((\<Prod>(xp, yp) \<leftarrow> l. pom xs xp)))"
    sorry
  also have "... = 
          (let (xs, ys) = hd (butlast l)
            in  ys / (podeljene_razlike2_proizvod xs l))"
    using podeljene_razlike2_proizvod_def 
    by simp
  also have "... = 
          (let (xs, ys) = hd l
            in  ys / (podeljene_razlike2_proizvod xs l))"
    using assms
    using pom_lema2
    (* by auto *) (* Zasto ne radi? Da li mu smeta razlika izmedju plavog l, ?l i narandzastog l? *) 
    sorry
  also have "... = podeljene_razlike2_nulti_sabirak l"
    by simp
  finally show ?case 
    by simp
(*
za brisanje

lemma glava_nije_rep_za_barem_2_interpolaciona_cvora:
  fixes l :: "(real \<times> real) list"
  assumes "length l > 1" "distinct (map fst l) = True"
  shows "fst (last l) - fst (hd l)  \<noteq> 0"

fun podeljene_razlike2_nulti_sabirak :: "(real \<times> real) list \<Rightarrow> real" where
  "podeljene_razlike2_nulti_sabirak l = 
     (let (xs, ys) = hd l
       in  ys / podeljene_razlike2_proizvod xs l)"

definition podeljene_razlike2_proizvod :: "real \<Rightarrow> (real \<times> real) list \<Rightarrow> real" where
  "podeljene_razlike2_proizvod xs l = (\<Prod>(xp, yp) \<leftarrow> l. pom xs xp)"

fun pom :: "real \<Rightarrow> real \<Rightarrow> real" where
  "pom xs xp = (if xp = xs then 1 else xs - xp)"
*)

qed


lemma podeljene_razlike2_pomocno_izracunavanje1_lema3:
  fixes l::"(real\<times>real) list"
  assumes "length l > 1" "distinct (map fst l)"
  shows "podeljene_razlike2_pomocno_izracunavanje1_definicija2 l = (podeljene_razlike2_nulti_sabirak (butlast l))/(fst (hd l) - fst (last l))"
  using assms 
  using podeljene_razlike2_pomocno_izracunavanje1_lema2 
  by auto



(* Pomocno izracunavanje2 *)

fun podeljene_razlike2_pomocno_izracunavanje2_definicija1 :: "(real \<times> real) list \<Rightarrow> real" where 
  "podeljene_razlike2_pomocno_izracunavanje2_definicija1 l =  
    (let (xs, ys) = last l in ys / podeljene_razlike2_proizvod xs l)"

value "podeljene_razlike2_pomocno_izracunavanje2_definicija1  [(1,2),(3::real,14::real)]"
value "(podeljene_razlike2_poslednji_sabirak (tl [(1,2),(3::real,14::real)]))/(fst (last [(1,2),(3::real,14::real)]) - fst (hd [(1,2),(3::real,14::real)]))"

lemma pom_lema3:
  fixes l::"(real\<times>real) list"
  assumes "length l > 1" "distinct (map fst l)"
  shows "last (tl l) = last l"
  by (metis Nitpick.size_list_simp(2) One_nat_def assms(1) last_tl less_numeral_extra(4))

lemma pom_lema4:
  fixes l::"(real\<times>real) list"
  assumes "length l > 1" "distinct (map fst l)"
  shows "pom (fst (last l)) (fst (hd l)) = fst (last l) - fst (hd l)"
  using assms(1) assms(2) glava_nije_rep_za_barem_2_interpolaciona_cvora by force

lemma podeljene_razlike2_pomocno_izracunavanje2_lema1:
  fixes l::"(real\<times>real) list"
  assumes "length l > 1" "distinct (map fst l)"
  shows "podeljene_razlike2_pomocno_izracunavanje2_definicija1 l = (podeljene_razlike2_poslednji_sabirak (tl l))/(fst (last l) - fst (hd l))"
proof (induction l rule: podeljene_razlike2_poslednji_sabirak.induct)
  case (1 l)
  have "(podeljene_razlike2_poslednji_sabirak (tl l))/(fst (last l) - fst (hd l)) = 
        (let (xs, ys) = last (tl l)
      in  ys/podeljene_razlike2_proizvod xs (tl l))/(fst (last l) - fst (hd l)) "
    by simp
  also have "... = 
        (let (xs, ys) = last (tl l)
      in  (ys/podeljene_razlike2_proizvod xs (tl l))/(fst (last l) - fst (hd l))) "
    by (simp add: case_prod_beta)
  also have "... =  
        (let (xs, ys) = last (tl l)
      in  ys/((fst (last l) - fst (hd l))*podeljene_razlike2_proizvod xs (tl l)))"
    by (simp add: case_prod_beta)
  also have "... =  
        (let (xs, ys) = last (tl l)
      in  ys/((fst (last l) - fst (hd l))*(\<Prod>(xp, yp) \<leftarrow> (tl l). pom xs xp)))"
    using podeljene_razlike2_proizvod_def
    by (simp add: case_prod_beta)
  also have "... =  
        (let (xs, ys) = last l
      in  ys/((fst (last l) - fst (hd l))*(\<Prod>(xp, yp) \<leftarrow> (tl l). pom xs xp)))"
    using pom_lema3
    by (smt case_prod_beta div_by_0 hd_conv_nth last_conv_nth last_tl length_tl list.size(3) mult.commute mult_cancel_right2)
  also have "... =  
        (let (xs, ys) = last l
      in  ys/((pom (fst (last l)) (fst (hd l)))*(\<Prod>(xp, yp) \<leftarrow> (tl l). pom xs xp)))"
    using pom_lema4
    sorry (*Zasto nece?*)
  also have "... =  
        (let (xs, ys) = last l
      in  ys/((pom xs (fst (hd l)))*(\<Prod>(xp, yp) \<leftarrow> (tl l). pom xs xp)))"
    by (simp add: case_prod_unfold)
  also have "... =  
        (let (xs, ys) = last l
      in  ys/(\<Prod>(xp, yp) \<leftarrow> l. pom xs xp))"
    sorry
  also have "... =  
        (let (xs, ys) = last l
      in  ys/podeljene_razlike2_proizvod xs l)"
    using podeljene_razlike2_proizvod_def 
    by simp
  also have "... = podeljene_razlike2_pomocno_izracunavanje2_definicija1 l"
    by simp
  finally show ?case
    by simp
qed
  
(*
za brisanje 

fun podeljene_razlike2_pomocno_izracunavanje2_definicija1 :: "(real \<times> real) list \<Rightarrow> real" where 
  "podeljene_razlike2_pomocno_izracunavanje2_definicija1 l =  
    (let (xs, ys) = last l in ys / podeljene_razlike2_proizvod xs l)"

fun pom :: "real \<Rightarrow> real \<Rightarrow> real" where
  "pom xs xp = (if xp = xs then 1 else xs - xp)"

fun podeljene_razlike2_proizvod :: "real \<Rightarrow> (real \<times> real) list \<Rightarrow> real" where
  "podeljene_razlike2_proizvod xs l = (\<Prod>(xp, yp) \<leftarrow> l. pom xs xp)"

definition podeljene_razlike2_poslednji_sabirak :: "(real \<times> real) list \<Rightarrow> real" where
  "podeljene_razlike2_poslednji_sabirak l = 
    (let (xs, ys) = last l
      in  ys /podeljene_razlike2_proizvod xs l)"
*)


(* Pomocno izracunavanje3 *)
fun podeljene_razlike2_pomocno_izracunavanje3_definicija1 :: "(real \<times> real) list \<Rightarrow> real" where 
  "podeljene_razlike2_pomocno_izracunavanje3_definicija1 l =  (\<Sum>(xs, ys) \<leftarrow> tl (butlast l). ((1/podeljene_razlike2_proizvod xs (tl l)) - (1/podeljene_razlike2_proizvod xs (butlast l)))*ys)"

value "(let l = [(1::real, 22::real), (3,4),(5,6),(711,8)] in podeljene_razlike2_pomocno_izracunavanje3_definicija1 l = podeljene_razlike2_bez_poslednjeg_sabirka (tl l) - podeljene_razlike2_bez_nultog_sabirka (butlast l))"


  
lemma neproverena_lema:
  fixes l::"(real\<times>real) list"
  fixes f::"((real\<times>real) list \<Rightarrow> (real\<times>real) list)"
  fixes g h::"(real \<Rightarrow> real \<Rightarrow> real)"
  assumes "length l > 1" "distinct (map fst l)"
  assumes "length (f l) > 1" "length (f l) = length l"
  shows "(\<Sum>(xs, ys) \<leftarrow> f l. (g xs ys) - (h xs ys)) = (\<Sum>(xs, ys) \<leftarrow> f l. (g xs ys)) - (\<Sum>(xs, ys) \<leftarrow> f l. (h xs ys))"
  sorry


lemma podeljene_razlike2_pomocno_izracunavanje3_lema1:
  fixes l::"(real\<times>real) list"
  assumes "length l > 1" "distinct (map fst l)"
  shows "podeljene_razlike2_pomocno_izracunavanje3_definicija1 l = podeljene_razlike2_bez_poslednjeg_sabirka (tl l) - podeljene_razlike2_bez_nultog_sabirka (butlast l)"
proof (induction l rule: podeljene_razlike2_pomocno_izracunavanje3_definicija1.induct)
  case (1 l)
  have "podeljene_razlike2_pomocno_izracunavanje3_definicija1 l = 
        (\<Sum>(xs, ys) \<leftarrow> tl (butlast l). ((1/podeljene_razlike2_proizvod xs (tl l)) - (1/podeljene_razlike2_proizvod xs (butlast l)))*ys )"
    by simp
  also have "... = 
        (\<Sum>(xs, ys) \<leftarrow> tl (butlast l). (ys/podeljene_razlike2_proizvod xs (tl l)) - (ys/podeljene_razlike2_proizvod xs (butlast l)) )"    
    by (simp add: mult.commute right_diff_distrib')
  also have "... = 
        (\<Sum>(xs, ys) \<leftarrow> tl (butlast l). (ys/podeljene_razlike2_proizvod xs (tl l))) -
        (\<Sum>(xs, ys) \<leftarrow> tl (butlast l). (ys/podeljene_razlike2_proizvod xs (butlast l)))"
    thm sum_list_subtractf
    sorry
  also have "... = 
    podeljene_razlike2_bez_poslednjeg_sabirka (tl l) -
    podeljene_razlike2_bez_nultog_sabirka (butlast l)"
    using podeljene_razlike2_bez_nultog_sabirka_def
    using podeljene_razlike2_bez_poslednjeg_sabirka_def
    by (simp add: butlast_tl)
  finally show ?case 
    by simp
qed

(* Pomocno izracunavanje4 *)
fun podeljene_razlike2_pomocno_izracunavanje4_definicija1 :: "(real \<times> real) list \<Rightarrow> real" where 
  "podeljene_razlike2_pomocno_izracunavanje4_definicija1 l =  
  (\<Sum>(xs, ys) \<leftarrow> tl (butlast l). 
    (((xs - fst (hd l))/podeljene_razlike2_proizvod xs l) - 
     ((xs - fst (last l))/podeljene_razlike2_proizvod xs l))*ys)"

lemma podeljene_razlike2_pomocno_izracunavanje4_lema1:
  fixes l::"(real\<times>real) list"
  assumes "length l > 1" "distinct (map fst l)"
  shows "podeljene_razlike2_pomocno_izracunavanje4_definicija1 l = podeljene_razlike2_pomocno_izracunavanje3_definicija1 l"
  sorry


(* Pomocno izracunavanje5 *)
fun podeljene_razlike2_pomocno_izracunavanje5_definicija1 :: "(real \<times> real) list \<Rightarrow> real" where 
  "podeljene_razlike2_pomocno_izracunavanje5_definicija1 l =  
  (\<Sum>(xs, ys) \<leftarrow> tl (butlast l). 
    ((fst (last l) - fst (hd l))/podeljene_razlike2_proizvod xs l)*ys)"

lemma podeljene_razlike2_pomocno_izracunavanje5_lema1:
  fixes l::"(real\<times>real) list"
  assumes "length l > 1" "distinct (map fst l)"
  shows "podeljene_razlike2_pomocno_izracunavanje5_definicija1 l = podeljene_razlike2_pomocno_izracunavanje4_definicija1 l"
  sorry

(* Pomocno izracunavanje6 *)
fun podeljene_razlike2_pomocno_izracunavanje6_definicija1 :: "(real \<times> real) list \<Rightarrow> real" where 
  "podeljene_razlike2_pomocno_izracunavanje6_definicija1 l =  
  (\<Sum>(xs, ys) \<leftarrow> tl (butlast l). ys/podeljene_razlike2_proizvod xs l)"

lemma podeljene_razlike2_pomocno_izracunavanje6_lema1:
  fixes l::"(real\<times>real) list"
  assumes "length l > 1" "distinct (map fst l)"
  shows "podeljene_razlike2_pomocno_izracunavanje6_definicija1 l = 
    podeljene_razlike2_pomocno_izracunavanje5_definicija1 l / (fst (last l) - fst (hd l))"
  sorry

(* Pomocno izracunavanje7 *)

lemma podeljene_razlike2_pomocno_izracunavanje7_lema1:
  fixes l::"(real\<times>real) list"
  assumes "length l > 1" "distinct (map fst l)"
  shows "(podeljene_razlike2_pomocno_izracunavanje1_definicija2 l) + 
      (podeljene_razlike2_pomocno_izracunavanje6_definicija1 l) + 
      (podeljene_razlike2_pomocno_izracunavanje2_definicija1 l) = podeljene_razlike2 l"
  sorry

(* glavno tvrdjenje *)
lemma 
  fixes l :: "(real \<times> real) list"
  assumes "l \<noteq> []" "distinct (map fst l)"
  shows "podeljene_razlike l = podeljene_razlike2 l"
  using assms
proof (induction l rule: podeljene_razlike.induct)
  case 1 (* podeljene_razlike [] = podeljene_razlike2 []  *)
  then show ?case 
    unfolding podeljene_razlike2_def
    by simp
next
  case (2 x y) (* podeljene_razlike [(x,y)] = podeljene_razlike2 [(x,y)] *)
  then show ?case 
    unfolding podeljene_razlike2_def
    unfolding podeljene_razlike2_proizvod_def
    by simp
next
  case (3 l0 l1 ls)
  let ?l = "l0 # l1 # ls"
  have "podeljene_razlike ?l = (podeljene_razlike (tl ?l) - podeljene_razlike (butlast ?l)) /
                               (fst (last ?l) - fst (hd ?l))"
    by simp
  also have "... = (podeljene_razlike2 (tl ?l) - podeljene_razlike2 (butlast ?l)) /
                   (fst (last ?l) - fst (hd ?l))"
    using 3
    unfolding podeljene_razlike2_def
    unfolding podeljene_razlike2_proizvod_def
    by (smt distinct_butlast distinct_tl divide_cancel_right hd_conv_nth last_conv_nth length_butlast list.distinct(1) list.sel(3) list.size(3) map_butlast map_tl)

  (* izvadimo n-ti sabirak sume iz prvog poziva podeljene_razlike2 *)
  also have "... = 
      ( podeljene_razlike2_bez_poslednjeg_sabirka (tl ?l) + 
        podeljene_razlike2_poslednji_sabirak (tl ?l) -
        podeljene_razlike2 (butlast ?l)
      ) /
      (fst (last ?l) - fst (hd ?l))"
    by (simp add: podeljene_razlike2_izvlacenje_n_tog_sabirka_sume)
  also have "... = 
      ( podeljene_razlike2_bez_poslednjeg_sabirka (tl ?l) + 
        podeljene_razlike2_poslednji_sabirak (tl ?l) -
        podeljene_razlike2_nulti_sabirak (butlast ?l) - 
        podeljene_razlike2_bez_nultog_sabirka (butlast ?l)
      ) /
      (fst (last ?l) - fst (hd ?l))"
    by (simp add: podeljene_razlike2_izvlacenje_0_tog_sabirka_sume)
  also have "... = 
      (podeljene_razlike2_bez_poslednjeg_sabirka (tl ?l))/(fst (last ?l) - fst (hd ?l)) + 
      (podeljene_razlike2_poslednji_sabirak (tl ?l))/(fst (last ?l) - fst (hd ?l)) -
      (podeljene_razlike2_nulti_sabirak (butlast ?l))/(fst (last ?l) - fst (hd ?l)) - 
      (podeljene_razlike2_bez_nultog_sabirka (butlast ?l))/(fst (last ?l) - fst (hd ?l))"
      find_theorems "(_ + _) / _ = _ / _ + _ / _"
      find_theorems "(_ - _) / _ = _ / _ - _ / _"
      by (simp add: add_divide_distrib diff_divide_distrib)
    also have "... = 
      (podeljene_razlike2_bez_poslednjeg_sabirka (tl ?l))/(fst (last ?l) - fst (hd ?l)) + 
      (podeljene_razlike2_poslednji_sabirak (tl ?l))/(fst (last ?l) - fst (hd ?l)) +
      (podeljene_razlike2_nulti_sabirak (butlast ?l))/(fst (hd ?l) - fst (last ?l)) - 
      (podeljene_razlike2_bez_nultog_sabirka (butlast ?l))/(fst (last ?l) - fst (hd ?l))"
      find_theorems "-(_/_) = _/(-_)"
      by (simp add: minus_divide_right)
    also have "... = 
      (podeljene_razlike2_nulti_sabirak (butlast ?l))/(fst (hd ?l) - fst (last ?l)) + 
      (podeljene_razlike2_bez_poslednjeg_sabirka (tl ?l) - podeljene_razlike2_bez_nultog_sabirka (butlast ?l))/(fst (last ?l) - fst (hd ?l)) + 
      (podeljene_razlike2_poslednji_sabirak (tl ?l))/(fst (last ?l) - fst (hd ?l))"
      find_theorems "_/?a - _/?a"
      by (simp add: diff_divide_distrib)
    also have "... = 
      (podeljene_razlike2_pomocno_izracunavanje1_definicija2 ?l) + 
      (podeljene_razlike2_bez_poslednjeg_sabirka (tl ?l) - podeljene_razlike2_bez_nultog_sabirka (butlast ?l))/(fst (last ?l) - fst (hd ?l)) + 
      (podeljene_razlike2_poslednji_sabirak (tl ?l))/(fst (last ?l) - fst (hd ?l))"
      using podeljene_razlike2_pomocno_izracunavanje1_lema3
      by (metis (no_types, lifting) "3.prems"(2) length_greater_0_conv length_tl list.sel(3) list.simps(3) zero_less_diff)
    also have "... = 
      (podeljene_razlike2_pomocno_izracunavanje1_definicija2 ?l) + 
      (podeljene_razlike2_bez_poslednjeg_sabirka (tl ?l) - podeljene_razlike2_bez_nultog_sabirka (butlast ?l))/(fst (last ?l) - fst (hd ?l)) + 
      (podeljene_razlike2_pomocno_izracunavanje2_definicija1 ?l)"
      using podeljene_razlike2_pomocno_izracunavanje2_lema1
      by (metis (no_types, lifting) "3.prems"(2) length_greater_0_conv length_tl list.sel(3) list.simps(3) zero_less_diff)
    also have "... = 
      (podeljene_razlike2_pomocno_izracunavanje1_definicija2 ?l) + 
      (podeljene_razlike2_pomocno_izracunavanje3_definicija1 ?l)/(fst (last ?l) - fst (hd ?l)) + 
      (podeljene_razlike2_pomocno_izracunavanje2_definicija1 ?l)"
      using podeljene_razlike2_pomocno_izracunavanje3_lema1
      by (metis (no_types, lifting) "3.prems"(2) length_greater_0_conv length_tl list.sel(3) list.simps(3) zero_less_diff)
    also have "... = 
      (podeljene_razlike2_pomocno_izracunavanje1_definicija2 ?l) + 
      (podeljene_razlike2_pomocno_izracunavanje4_definicija1 ?l)/(fst (last ?l) - fst (hd ?l)) + 
      (podeljene_razlike2_pomocno_izracunavanje2_definicija1 ?l)"
      using podeljene_razlike2_pomocno_izracunavanje4_lema1
      by (metis (no_types, lifting) "3.prems"(2) length_greater_0_conv length_tl list.sel(3) list.simps(3)  zero_less_diff)
    also have "... = 
      (podeljene_razlike2_pomocno_izracunavanje1_definicija2 ?l) + 
      (podeljene_razlike2_pomocno_izracunavanje5_definicija1 ?l)/(fst (last ?l) - fst (hd ?l)) + 
      (podeljene_razlike2_pomocno_izracunavanje2_definicija1 ?l)"
      using podeljene_razlike2_pomocno_izracunavanje5_lema1
      by (metis (no_types, lifting) "3.prems"(2) length_Cons length_tl list.sel(3) zero_less_Suc zero_less_diff)
    also have "... = 
      (podeljene_razlike2_pomocno_izracunavanje1_definicija2 ?l) + 
      (podeljene_razlike2_pomocno_izracunavanje6_definicija1 ?l) + 
      (podeljene_razlike2_pomocno_izracunavanje2_definicija1 ?l)"
      using podeljene_razlike2_pomocno_izracunavanje6_lema1
      by (metis (no_types, lifting) "3.prems"(2) length_Cons length_tl list.sel(3) zero_less_Suc zero_less_diff)
    also have "... = podeljene_razlike2 ?l"
      using podeljene_razlike2_pomocno_izracunavanje7_lema1
      by (metis "3.prems"(2) length_Cons length_tl list.sel(3) zero_less_Suc zero_less_diff)
  finally
  show ?case
    by simp
qed


(* 

x:    [0.992, 0.995, 1.008, 1.012, 1.018, 1.021] 
f(x): [-0.0084, -0.0080, -0.0065, -0.0060, -0.0053, -0.0049]

xi     f(xi)   f[xi,xi+1]   f[xi,xi+1,xi+2]   f[xi,xi+1,xi+2,xi+3]  
0.992 -0.0084   0.13333        -1.12188             84.38800
0.995 -0.0080   0.11538         0.56588            -60.82087
1.008 -0.0065   0.12500        -0.83300            206.47000
1.012 -0.0060   0.11667         1.85111
1.018 -0.0053   0.13333
1.021 -0.0049


*)
value "podeljene_razlike (zip [1.008, 1.012, 1.018]  [-0.0065, -0.0060, -0.0053])"
value "podeljene_razlike2 (zip [1.008, 1.012, 1.018]  [-0.0065, -0.0060, -0.0053])"

end