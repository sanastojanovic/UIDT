theory mi17272_Ana_Nikacevic
  imports  Complex_Main 

begin

text \<open>

link: https://www.imo-official.org/problems/IMO2006SL.pdf
Algebra Problem A4

Dokazati nejednakost:

sum (i<j) (ai*aj/(ai+aj)) <= n/2*(a1+a2+...+an) * sum (i<j) (ai*aj)

\<close>
type_synonym lista = "real list "


primrec duzina :: "lista \<Rightarrow> nat" where
"duzina [] = 0" |
"duzina (x # xs) = 1+duzina xs"

fun umnozi :: "nat \<Rightarrow> real \<Rightarrow> lista" where
"umnozi 0 _ = []" |
"umnozi x y = y # (umnozi (x-1) y) " 


fun prvi_elementi_pomocna :: "nat \<Rightarrow> lista \<Rightarrow> lista" where 
"prvi_elementi_pomocna _ [] = [] " |
"prvi_elementi_pomocna _ [x] = [] " |
"prvi_elementi_pomocna n (x # xs) = umnozi n x @ prvi_elementi_pomocna (n-1) xs "


abbreviation prvi_elementi :: "lista \<Rightarrow> lista" where 
"prvi_elementi l \<equiv> prvi_elementi_pomocna ((duzina l)-1) l "


primrec veci_od :: "lista \<Rightarrow> real \<Rightarrow> lista " where
"veci_od  [] a = []  " |
"veci_od (x# xs) a = (if x> a then ([x] @ veci_od xs a ) else veci_od xs a) " 

fun drugi_elementi_pomocna :: "nat \<Rightarrow> lista  \<Rightarrow> lista" where 
"drugi_elementi_pomocna 0  _ = []  " | 
"drugi_elementi_pomocna i l =  (veci_od l (l ! (duzina l-i  ) )) @ drugi_elementi_pomocna  (i-1) l  "

abbreviation drugi_elementi :: "lista  \<Rightarrow> lista" where 
"drugi_elementi l \<equiv> drugi_elementi_pomocna (duzina l) l"

value "prvi_elementi [1,2,3,4]"
value "drugi_elementi [1,2,3,4]"

fun prva_suma_pom :: "nat \<Rightarrow> lista \<Rightarrow> real" where
"prva_suma_pom 0 l = ((prvi_elementi l) ! 0 * (drugi_elementi l) ! 0 )  / ( ((prvi_elementi l) ! 0) + ((drugi_elementi l) ! 0 ))  " |
"prva_suma_pom i l = (   ((prvi_elementi l) ! i) * ((drugi_elementi l) ! i ) / ( ((prvi_elementi l) ! i) + ((drugi_elementi l) ! i ) )  ) + prva_suma_pom (i-1) l "

definition prva_suma :: "lista  \<Rightarrow> real" where 
"prva_suma l = prva_suma_pom (duzina (prvi_elementi l)-1) l  "

fun druga_suma_pom :: "nat \<Rightarrow> lista \<Rightarrow> real" where
"druga_suma_pom 0 l = ((prvi_elementi l) ! 0 * (drugi_elementi l) ! 0 ) " |
"druga_suma_pom i l = (((prvi_elementi l) ! i) * ((drugi_elementi l) ! i )) + druga_suma_pom (i-1) l "

definition druga_suma :: "lista  \<Rightarrow> real" where 
"druga_suma l = druga_suma_pom (duzina (prvi_elementi l)-1) l  "

fun suma_zbira_pom :: "nat \<Rightarrow> lista \<Rightarrow> real" where
"suma_zbira_pom 0 l = ((prvi_elementi l) ! 0 + (drugi_elementi l) ! 0 ) " |
"suma_zbira_pom i l = (((prvi_elementi l) ! i) + ((drugi_elementi l) ! i )) + suma_zbira_pom (i-1) l "

abbreviation suma_zbira_dva_elem :: "lista  \<Rightarrow> real" where 
"suma_zbira_dva_elem l \<equiv> suma_zbira_pom (duzina (prvi_elementi l)-1) l  "


definition suma_kvadrata_bez_odredjenog_indeksa :: "lista \<Rightarrow> nat \<Rightarrow> real" where
  "suma_kvadrata_bez_odredjenog_indeksa li i = (sum_list li)*(li!i) - (li!i*li!i)"

lemma izraz_na_kvadrat_kroz_izraz:
  fixes a b::real
  shows "(a+b)^2 / (a+b) =a+b  "
proof-
  have "(a+b)^2 / (a+b) = (a+b)*(a+b)/(a+b)" by (auto simp add:  Power.monoid_mult_class.power2_eq_square)
  then show "(a+b)^2 / (a+b) = (a+b)" by auto
qed

lemma sum_list_extract_2:
  fixes l :: "real list" 
  assumes "i < length l" "j < length l" "i \<noteq> j" 
  shows "sum_list l = (l ! i) + (l ! j) + (\<Sum> k | k < length l \<and> k \<noteq> i \<and> k \<noteq>
j. l ! k)"
proof-
  have *: "{k. k < length l} = {k. k < length l \<and> k \<noteq> i \<and> k \<noteq> j} \<union> {i, j}"
    using assms
    by auto
  have "sum_list l = (\<Sum> k | k < length l. l ! k)"
    by (metis atLeastLessThan_iff mem_Collect_eq subsetI subset_antisym
sum_list_sum_nth zero_le)
  also have "... = (\<Sum> k \<in> {k. k < length l \<and> k \<noteq> i \<and> k \<noteq> j} \<union> {i, j}. l !k)"
    using *
    by auto
  also have "... = (\<Sum> k | k < length l \<and> k \<noteq> i \<and> k \<noteq> j. l ! k) + (\<Sum> k \<in> {i,j}. l ! k)"
    by (rule sum.union_disjoint, auto)
  finally
  show ?thesis
    using assms
    by auto
qed

lemma sum_list:
  fixes l :: "real list"
  assumes  "i < length l" "j < length l" "i \<noteq> j" "\<forall> x \<in> set l. x > 0"  "length li \<ge> 2"
  shows "sum_list l \<ge> (l ! i) + (l ! j)"
proof-
  have *:"(\<Sum> k | k < length l \<and> k \<noteq> i \<and> k \<noteq> j. l ! k) \<ge> 0"
    by (smt (verit) assms(4) mem_Collect_eq nth_mem sum_nonneg)
  have "(l ! i) + (l ! j) > 0"
    by (smt (z3) assms(1) assms(2) assms(4) nth_mem)
  from this * show  ?thesis 
    using sum_list_extract_2[OF assms(1-3)]
    by auto
qed


lemma suma_svih_vecih_od_nula:
  fixes l :: "lista"
  assumes "i < length l" "j < length l" "i \<noteq> j" "\<forall> x \<in> set l. x > 0"  "length li \<ge> 2"
  shows   " sum_list l  > 0"
  using assms
  by (smt (verit) nth_mem sum_list)

  
lemma suma_dva_vecih_od_nula:
  fixes l :: "lista"
  assumes "i < length l" "j < length l" "i \<noteq> j" "\<forall> x \<in> set l. x > 0"  "length li \<ge> 2"
  shows "(l ! i) + (l ! j) > 0"
  by (meson assms(1) assms(2) assms(4) in_set_conv_nth pos_add_strict)


fun indeks_elem' :: "lista \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat" where
"indeks_elem' [] _  br = br" |
"indeks_elem' (x#xs) a br = (if a=x then br else indeks_elem' xs a (br+1))"

definition indeks_elem :: "lista \<Rightarrow> real \<Rightarrow> nat" where
"indeks_elem li x= indeks_elem' li x 0 "

value "indeks_elem [1,2,3,4,7,2::real] 3 "

(* Drugi pristup *)
lemma pomocna_nejednakost1:
  fixes i j::nat and li:: lista
   assumes "i < length li" "j < length li" "i \<noteq> j" "\<forall> x \<in> set li. x > 0"  "length li \<ge> 2"
  shows "4 * (li ! i)*(li ! j)/((li ! i) + (li ! j))  \<le> ((suma_kvadrata_bez_odredjenog_indeksa li i) +( suma_kvadrata_bez_odredjenog_indeksa li j) + 2* (li ! i)*(li ! j))/sum_list li "
proof -
  have pom1:"4*(li!i)*(li!j)/((li!i)+(li!j))= ((li!i)^2 + (li!j)^2 + 2* (li!i)*(li!j)- (li!i)^2+2*(li!i)*(li!j)-(li!j)^2)/((li!i)+(li!j))" using assms  by auto
  then have pom2:"((li!i)^2 + (li!j)^2 + 2* (li!i)*(li!j)- (li!i)^2+2*(li!i)*(li!j)-(li!j)^2)/((li!i)+(li!j)) = ((li!i+li!j)^2- ((li!i-li!j)^2))/(li!i+li!j)"  using assms by (auto simp add:  Power.comm_semiring_1_class.power2_sum  Power.comm_ring_1_class.power2_diff)
  then have pom3:"((li!i+li!j)^2- ((li!i-li!j)^2))/(li!i+li!j) = ((li!i+li!j)^2/(li!i+li!j)) - ((li!i-li!j)^2/(li!i+li!j)) " using assms by (auto simp add: Fields.division_ring_class.diff_divide_distrib)
  then have pom4:"((li!i+li!j)^2/(li!i+li!j)) - ((li!i-li!j)^2/(li!i+li!j)) =  li!i+li!j - ((li!i-li!j)^2/(li!i+li!j))" using assms  by (auto simp add:izraz_na_kvadrat_kroz_izraz)  
  have p0:"sum_list li > 0 " using suma_svih_vecih_od_nula[OF assms(1-5)] by auto
  have p1:"(li!i+li!j) \<le> (sum_list li) " using assms sum_list[OF assms(1-5)] by auto
  have p2:"(li!i-li!j)^2 \<ge> 0 " by auto
  have p3:"(li!i+li!j) * (sum_list li) > 0 " using assms suma_dva_vecih_od_nula[OF assms(1-5)] suma_svih_vecih_od_nula[OF assms(1-5)] by auto
  have pom5: "((li!i-li!j)^2/(sum_list li)) \<le>  ((li!i-li!j)^2/(li!i+li!j))" using p1 p2 p3  by (auto simp: field_simps divide_left_mono)
  then have pom6:"(li!i+li!j) - ((li!i-li!j)^2/(li!i+li!j)) \<le> (li!i+li!j) - ((li!i-li!j)^2/(sum_list li))" using assms by auto
  then have pom7:"(li!i+li!j) - ((li!i-li!j)^2/(sum_list li)) =((li!i)*(sum_list li)+(li!j)*(sum_list li)- (li!i-li!j)^2)/(sum_list li) " using assms p0 by (metis diff_divide_eq_iff less_numeral_extra(3) ring_class.ring_distribs(2))
  let ?bez_i = "suma_kvadrata_bez_odredjenog_indeksa li i "
  let ?bez_j = "suma_kvadrata_bez_odredjenog_indeksa li j"
 let ?ostatak = "(li!i-li!j)^2"
  have p4:"?bez_i = (li!i)*(sum_list li)  - (li!i)*(li!i)" using assms unfolding suma_kvadrata_bez_odredjenog_indeksa_def by auto
  have p5:"?bez_j = (li!j)*(sum_list li)  - (li!j)*(li!j)" using assms unfolding suma_kvadrata_bez_odredjenog_indeksa_def by auto
  have " (li!i-li!j)^2 = ((li!i)^2-2*li!i*li!j+(li!j)^2)" using assms by (simp add: power2_diff)
  then have p6:"?ostatak =(li!i)*(li!i)-2*li!i*li!j+(li!j)*(li!j)"  using assms by (auto simp add: power2_eq_square) 
  have p7:"((li!i)*(sum_list li)+(li!j)*(sum_list li)- (li!i-li!j)^2) = (li!i)*(sum_list li) + (li!j)*(sum_list li) - (li!i)*(li!i)+2*li!i*li!j-(li!j)*(li!j)"  
    using p6 by auto
  then have "(li!i)*(sum_list li) + (li!j)*(sum_list li) - (li!i)*(li!i)+2*li!i*li!j-(li!j)*(li!j) = ?bez_i + ?bez_j +2*li!i*li!j" using p4 p5 by auto  
  have  "((li!i)*(sum_list li)+(li!j)*(sum_list li)- (li!i-li!j)^2)/(sum_list li) = (?bez_i + ?bez_j+2*li!i*li!j)/(sum_list li) "
    using assms p0 
    by (simp add: assms(5) p4 p5 p7)
  from this   show ?thesis 
     unfolding suma_kvadrata_bez_odredjenog_indeksa_def 
     by (metis pom1 pom2 pom3 pom4 pom6 pom7)
 qed

definition prva_suma_preko_dve_sume_pom :: "lista \<Rightarrow> nat \<Rightarrow> real" where
  "prva_suma_preko_dve_sume_pom li i = sum_list( map (\<lambda>x . (x*(li!i)/( x+(li!i))))   (filter (\<lambda>x . indeks_elem li x \<noteq> i)  li))"

value "prva_suma_preko_dve_sume_pom [1,2,3::real] 0"

definition prva_suma_preko_dve_sume  :: "lista \<Rightarrow> real" where
"prva_suma_preko_dve_sume li = sum_list (map (\<lambda>x .(prva_suma_preko_dve_sume_pom li x )) [0..<length li] ) "   

definition prva_suma_i_manje_od_j_pom :: "lista \<Rightarrow> nat \<Rightarrow> lista" where
  "prva_suma_i_manje_od_j_pom li i =  map (\<lambda>x . (x*(li!i)/( x+(li!i)))) (filter (\<lambda>x . indeks_elem li x < i)  li)"

definition prva_suma_i_manje_od_j  :: "lista \<Rightarrow> real" where
"prva_suma_i_manje_od_j li = sum_list (map (\<lambda>x .   (sum_list (prva_suma_i_manje_od_j_pom li x)) ) [0..<length li] ) "   


definition druga_suma_i_manje_od_j_pom :: "lista \<Rightarrow> nat \<Rightarrow> lista" where
  "druga_suma_i_manje_od_j_pom li i =  map (\<lambda>x . (x*(li!i)))   (filter (\<lambda>x . indeks_elem li x < i)  li)"


definition druga_suma_i_manje_od_j  :: "lista \<Rightarrow> real" where
"druga_suma_i_manje_od_j li = sum_list (map (\<lambda>x .   (sum_list (druga_suma_i_manje_od_j_pom li x)) ) [0..<length li] ) "   

definition suma_zbir_dva_elem_pom :: "lista \<Rightarrow> nat \<Rightarrow> real" where
  "suma_zbir_dva_elem_pom li i = sum_list( map (\<lambda>x .x+(li!i) )   (filter (\<lambda>x . indeks_elem li x < i)  li))"

value "suma_zbir_dva_elem_pom [1,2,3::real] 2"

definition suma_zbir_dva_elem  :: "lista \<Rightarrow> real" where
"suma_zbir_dva_elem li = sum_list (map (\<lambda>x .(suma_zbir_dva_elem_pom li x )) [0..<length li] ) "   

value "suma_zbir_dva_elem [1,2,3::real]"

definition suma_razlika_kvadrata_pom :: "lista \<Rightarrow> nat \<Rightarrow> real" where
  "suma_razlika_kvadrata_pom li i = sum_list( map (\<lambda>x . (x-(li!i))^2/(x+(li!i)) )   (filter (\<lambda>x . indeks_elem li x < i)  li))"

value "suma_razlika_kvadrata_pom [1,2,3::real] 2"

definition suma_razlika_kvadrata  :: "lista \<Rightarrow> real" where
"suma_razlika_kvadrata li = sum_list (map (\<lambda>x .(suma_razlika_kvadrata_pom li x )) [0..<length li] ) "   

value "suma_razlika_kvadrata [1,2,3::real]"
(*
lemma prva_nejednakost_drugog_dela:
  fixes  li:: lista
   assumes  "\<forall> x \<in> set li. x > 0"  "length li \<ge> 2"  "i< length li"  "j< length li"    
   shows "1/2*(\<Sum> i \<leftarrow> [0..<length li]. prva_suma_preko_dve_sume_pom li i)
   \<le> 1/8*(\<Sum> i \<leftarrow> [0..<length li]. ((suma_kvadrata_bez_odredjenog_indeksa li i)
 +( suma_kvadrata_bez_odredjenog_indeksa li j) + 2* (li ! i)*(li ! j))/sum_list li)   "
*)

lemma prva_jednakost_drugog_dela:
  fixes  li:: lista
   assumes  "\<forall> x \<in> set li. x > 0"  "length li \<ge> 2"
   shows "(prva_suma_i_manje_od_j li) = 1/2*(prva_suma_preko_dve_sume li)"
  sorry
(*   let ?p= "{(i,j). i < length li \<and>  j<length li \<and> i<j}"
  let ?d= "{(i,j). i < length li \<and>  j<length li \<and> i\<noteq>j}"
*)

(* Prvi pristup *)
lemma lema_bez_dokaza1:
  fixes li::lista
   assumes "i < duzina li" "j < duzina li" "i \<noteq> j" "\<forall> x \<in> set li. x \<ge> 0"
   shows "suma_zbir_dva_elem li = ((duzina li) -1 ) * (sum_list li)"
  sorry


lemma pomocna_jed_bez_sume:
  fixes a b::real
  assumes "a>0" "b>0"
  shows "1/4 * (a+b-(a-b)^2/(a+b)) = a*b/(a+b)"
proof-
  have p1:"1/4* (a+b - ((a-b)^2)/(a+b))= 1/4*((a+b)^2/(a+b) -(a-b)^2/(a+b))"
    by (simp add: izraz_na_kvadrat_kroz_izraz)
  from this have " 1/4*((a+b)^2/(a+b) -(a-b)^2/(a+b)) = 1/4*((a+b)^2/(a+b) -(a-b)^2/(a+b)) "
    by (simp add: diff_divide_distrib)
  from this  have p3:"1/4*((a+b)^2/(a+b) -(a-b)^2/(a+b)) =1/4*( (a^2+2*a*b+b^2)/(a+b) - (a^2-2*a*b+b^2)/(a+b))"
    by (auto simp add:field_simps  power2_sum power2_diff)
  from this have p4:"1/4*( (a^2+2*a*b+b^2)/(a+b) - (a^2-2*a*b+b^2)/(a+b))  = 1/4*((a^2+2*a*b+b^2-a^2+2*a*b-b^2)/(a+b))"
    using assms
    by (smt (verit, ccfv_SIG) diff_divide_distrib)   
  from this have "1/4*((a^2+2*a*b+b^2-a^2+2*a*b-b^2)/(a+b)) = a*b/(a+b)"
    by auto
  then show "1/4 * (a+b-(a-b)^2/(a+b)) = a*b/(a+b) "
    using p1 p3 p4 by presburger

qed

lemma jednakost_za_levu_stranu:
  fixes li::lista
  assumes "i < duzina li" "j < duzina li" "i \<noteq> j" "\<forall> x \<in> set li. x \<ge> 0"
shows "prva_suma_i_manje_od_j li = ((duzina li)-1)/4* (sum_list li) - 1/4*suma_razlika_kvadrata li  "
proof-
  have  "(\<Sum>k | i < length li \<and> j< length li \<and> i<j . (li!i * li!j)/(li!i+li!j)) =
   1/4*(\<Sum>k | i < length li \<and> j< length li \<and> i<j . li!i + li!j - ((li!i + li!j)^2)/(li!i+li!j))"
    using assms pomocna_jed_bez_sume sorry

  then show ?thesis sorry

qed

lemma glavna_nejednakost:
  fixes  li:: lista
   assumes  "\<forall> x \<in> set li. x > 0"  "length li \<ge> 2"
   shows "(prva_suma_i_manje_od_j li) \<le>
    ((duzina li)/(2*(sum_list li))) * (druga_suma_i_manje_od_j li) "
  oops
