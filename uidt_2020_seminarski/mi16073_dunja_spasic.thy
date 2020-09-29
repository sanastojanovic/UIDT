theory mi16073_dunja_spasic
  imports Complex_Main

begin

text\<open>
https://imomath.com/srb/zadaci/2017_egmo.pdf

Zadatak: Dat je prirodan broj n\<ge>1, kao i prirodni brojevi t1 < t2 < ... < tn.
U grupi od tn + 1 ljudi odigran je neki broj partija šaha.
Svake dve osobe su međusobno odigrale najviše jednu partiju.
Dokazati da je moguće da su sledeća dva uslova istovremeno zadovoljena:

(i) Broj partija koju je odigrala svaka od osoba je jedan od brojeva t1, t2, . . . , tn.
(ii) Za svako i za koje važi 1 \<le> i \<le> n, bar jedna osoba je odigrala tačno ti partija.

\<close>

(*U bool matrici tn+1 x tn+1 se čuva ko je sa kim odigrao partiju šaha.
Matrica je zadata tipom b_mat, a red u matrici tipom b_list.*)

type_synonym b_list = "bool list"
type_synonym b_mat = "b_list list"

(*Funkcija b_kv proverava da li je bool matrica kvadratna.*)

definition b_kv :: "b_mat \<Rightarrow> bool" where
" b_kv a = If (a = []) False (size_list length a =(length a)*(1+length a))"

value "b_kv [[True, False], [True, True]]"
value "b_kv [[True, False, False],[True, False, False],[True, False, False]]"
value "b_kv [[True, False, False, True],[True, False, False, True],[True, False, False, True], [True, False, False, False]]"

(*Funkcija prvi vraca prvi element bool liste.*)

fun prvi :: "bool list \<Rightarrow> bool" where
"prvi [] = False"
|"prvi (x # l) = x"

value "prvi [True, False, True]"

(*Funkcija partije_l od bool matrice pravi listu koja čuva koliko je svaki igrač odigrao partija.*)

fun partije_l :: "b_mat \<Rightarrow> nat list" where
"partije_l M = map (\<lambda> x. length (filter (\<lambda> a. a = True) x)) M"

lemma len_partije[simp]:
"length (partije_l x) = length x"
  by simp

(*Provera da li partije_l ispravno radi.*)

value "partije_l [[True, False, True, True], [True, False], [False], []]"


(*bez_pr je funkcija koja brise prvi element u listi.*)

fun bez_pr :: "'a list \<Rightarrow>'a list" where
"bez_pr [] = []"
| "bez_pr (Cons x l) = l"

lemma pom_bez_pr[simp]:
"bez_pr (a # l) = l"
  by simp

lemma sort_bez_pr[simp]:
  assumes "sorted l"
  shows "sorted (bez_pr l)"
  by (metis assms bez_pr.simps(1) bez_pr.simps(2) sorted.elims(2))

(*obr_prve brise prve elemente svakog reda u bool matrici.*)

fun obr_prve :: "b_mat \<Rightarrow> b_mat" where
"obr_prve [] = []"
| "obr_prve ([] # l) = obr_prve l"
| "obr_prve ((x # y) # l) = y # (obr_prve l)"

lemma pom:
  fixes a::bool and x::b_list and xs::b_mat
  shows "length (x # xs) = length ((a # x) # xs)"
  by simp

lemma smanjivanje [simp]:
  shows "length (obr_prve l) < Suc (length l)"
proof (induction l)
  case Nil
  show ?case
    by auto
next
  case (Cons x l)
  show ?case
  proof (induction x)
    case Nil
    show ?case
      using Cons by simp
  next
    case (Cons a x)
    show ?case
    proof -
      have "obr_prve ((a # x) # l) =  x # (obr_prve l)"
        by auto
      then have "length (obr_prve ((a # x) # l)) = length (x # (obr_prve l))"
        by auto
      also have "length (obr_prve ((a # x) # l)) = Suc (length (obr_prve l))"
        by auto
      also have "length (obr_prve ((a # x) # l)) = 1 + length (obr_prve l)"
        by auto
     note ih = `length (obr_prve l) < Suc (length l)`
      then have "length (obr_prve ((a # x) # l)) \<le> Suc (length l)"
      using ih by simp
    also have "Suc (length l) < Suc (length (x # l))"
      by simp
    also have  "Suc (length (x # l)) = Suc (length ((a # x) # l))"
      using pom by auto
    from this `Suc (length l) < Suc (length (x # l))` have "Suc (length l) < Suc (length ((a # x) # l))"
      by simp
    from this `length (obr_prve ((a # x) # l)) \<le> Suc (length l)`
    show ?thesis
      by simp
  qed
qed
qed


value "obr_prve [[True, False],[True],[True, False, False]]"
value "size_list length (obr_prve [[True, False],[True],[True, False, False]])"

(*Funkcija koja od zadate bool matrice nalazi njenu gornje trougaonu matricu.*)

fun gore_tr :: "b_mat \<Rightarrow> b_mat" where
"gore_tr [] = []"
| "gore_tr (x # l) = x # obr_prve ( gore_tr l)"

value "sim_mat [[True]]"


fun dodaj_kol :: "b_list \<Rightarrow> b_mat \<Rightarrow> b_mat" where
"dodaj_kol [] [] = []" |
"dodaj_kol (x # l) [] = []" |
"dodaj_kol [] (Cons xm M) = Cons xm M" |
"dodaj_kol (x # l) (Cons xm M) = (x # xm) # (dodaj_kol l M)"

value "dodaj_kol [True, False, True, True] [[True, False], [False], [False]]"

fun troug_u_sim :: "b_mat \<Rightarrow> b_mat" where
"troug_u_sim [] = []"
| "troug_u_sim (x # l) = x # (dodaj_kol (tl x) (troug_u_sim l))"

value "troug_u_sim [[True, False, False],[True, False],[True]]"

value "gore_tr [[True, False, True], [False, True, False], [False, False, True]]"

(*Funkcija koja vraca da li je matrica trougaona, sa glavnom dijagonalom false.*)

fun troug :: "b_mat \<Rightarrow> bool" where
"troug [] \<longleftrightarrow> True"
|"troug (Cons x l) \<longleftrightarrow> (troug l) \<and> (1 + length l = length x) \<and> (\<not> prvi x)"

lemma gore_tr_sim[simp]:
  assumes "troug T"
  assumes "M = troug_u_sim T"
  shows "gore_tr M = T"
  sorry

lemma obr_troug[simp]:
  assumes "troug M1"
  shows "troug (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) M1)"
  sorry

value "tl [1::nat, 9, 9]"

(*Provera da li ispravno radi trougaona matrica.*)
value "troug [[False, True, True],[False, True], [False]]"
value "size_list length [[],[[]]]"

(*Lema fiksira n i listu od t1 do tn. Pokazuje da postoji takva trougaona bool matrica p,
sa False na glavnoj dijagonali, za koju istovremeno mogu da važe uslovi (i) i (ii) iz zadatka.*)

(*Funkcija pocetni izdvaja sve pocetne elemente redova bool matrice u bool listu.*)

fun pocetni :: "b_mat \<Rightarrow> b_list" where
"pocetni [] = []"
| "pocetni (x # l) = (prvi x) # (pocetni l)"

value "pocetni [[True, False],[True, False], []]"

value "size_list length[[True,False,True],[True,True,False],[False,False,False]]"


(*Provera da li je matrica simetricna: Direktno proveriti u jednoj funkciji, tako sto se
proverava da li je simetricna matrica kojoj se obrise prva kolona i prvi red i a li su prva kolona i
prvi red jednaki, a onda rekurzivno to primeniti da ostatak matrice.*)
(*Funkcija sim_mat*)

function sim_mat :: "b_mat \<Rightarrow> bool" where
"sim_mat [] \<longleftrightarrow> True"
| "sim_mat ([] # l) \<longleftrightarrow>  False"
| "sim_mat ((x # y) # l) \<longleftrightarrow> (b_kv (obr_prve l) \<or> l = [])
  \<and> (length y = length l) \<and> (y = (pocetni l)) \<and> sim_mat (obr_prve l)"
  by pat_completeness auto
termination 
  apply (relation "measure (\<lambda> m. length m)")
   apply auto
  done

value "sim_mat [[],[],[]]"
value "sim_mat [[True, False], []]"
value "sim_mat [[True, True],[True, True]]"
value "sim_mat [[False, True, False], [True, False, True], [False, True, False]]"
value "sim_mat [[False, False], []]"
value " troug (gore_tr [[True, True, False], [True, False, False], [False, False, False]])"
value " troug (gore_tr [[False, True, False], [True, False, False], [False, False, False]])"
value "[] # []::b_mat"
value "sim_mat (troug_u_sim [[True, False, False],[True, False],[True]])"
value "troug_u_sim [[True, False, False],[True, False],[True]]"



lemma gore_tr_u_sim[simp]:
  assumes "troug M"
  shows "sim_mat (troug_u_sim M)"
  sorry

lemma mat_tr_sim[simp]:
  assumes "sim_mat M"
  assumes "troug (gore_tr M)"
  shows "M = troug_u_sim (gore_tr M)"
  sorry



fun sve_true :: "b_list \<Rightarrow> bool" where
"sve_true [] \<longleftrightarrow> True" |
"sve_true (Cons x xs) \<longleftrightarrow> x \<and> (sve_true xs)"

value "sve_true [True, True, False]"

fun lista_b_n ::"nat\<Rightarrow>b_list" where
"lista_b_n 0 = []"
| "lista_b_n (Suc n) = True # (lista_b_n n)"

fun lista_nat_n ::"nat \<Rightarrow> nat \<Rightarrow> nat list" where
"lista_nat_n n 0 = []"
| "lista_nat_n n (Suc m) = n # (lista_nat_n n m)"

value "lista_nat_n 4 14"

lemma skup_iste_liste[simp]:
  assumes "n > 0"
  shows "set (lista_nat_n (x) (n)) = {x}"
  using assms
proof (induction n)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  have "lista_nat_n (x) (Suc n) = x # (lista_nat_n x n)"
    by simp
  from this have "set (lista_nat_n (x) (Suc n)) = {x} \<union> set (lista_nat_n x n)"
    by simp
  from this have "... = {x} \<union> {x}"
    using Suc  by force
  then show ?case
    by simp
qed

fun jed :: "b_mat \<Rightarrow> bool" where
"jed [] \<longleftrightarrow> True" |
"jed (Cons x l) \<longleftrightarrow> (troug l) \<and> (1 + length l = length x) \<and> (\<not> prvi x) \<and> (sve_true (bez_pr x)) \<and> jed l"

fun nap_jed :: "nat \<Rightarrow> b_mat" where
"nap_jed 0 = []"
| "nap_jed (Suc n) = (False # (lista_b_n n)) # (nap_jed n)"

value "troug (nap_jed 7)"

lemma nap_jed_lema[simp]:
  "jed (nap_jed n)"
  sorry

fun dop_do_jed :: "nat \<Rightarrow> b_mat \<Rightarrow> b_mat" where
"dop_do_jed 0 M = M"
| "dop_do_jed n [] = nap_jed n"
| "dop_do_jed n (Cons x M) = (x @ lista_b_n n) # (dop_do_jed n M)"

value "dop_do_jed 3 [[False, True], [False]]"

lemma len_dop[simp]:
  assumes "n > 0"
  shows "length (dop_do_jed n M) = n + length M"
  sorry

lemma trug_dop[simp]:
  assumes "troug M"
  shows "troug (dop_do_jed n M)"
sorry

value "troug  [[False, True, True],[False, True],[False]]"
value "troug (gore_tr (troug_u_sim (dop_do_jed 3 [[False, True, True],[False, True],[False]])))"
value "troug_u_sim (dop_do_jed 3 [[],[],[]])"
value "troug_u_sim (dop_do_jed 1 [[False, True], [False]])"
value "partije_l (troug_u_sim (dop_do_jed 1[[False, True], [False]]))"
value "map (\<lambda> x. x + 1) (partije_l [[False, True], [False]]) @ (lista_nat_n (2+1-1) 1)"

lemma parije_dodate[simp]:
  assumes "n  > 0"
  assumes "length M > 0"
  assumes "troug M"
  shows "partije_l (troug_u_sim (dop_do_jed n M)) =
  (map (\<lambda> x. x + n)(partije_l (troug_u_sim M))) @ (lista_nat_n (length M + n - 1) n)"
  sorry

value "dop_do_jed 3 [[False, True], [False]]"

value "jed [[False, True, True], [False, True], [False]]"
value "troug [[False, True, True], [False, False], [False]]"

lemma smanjen_sim[simp]:
  assumes "sim_mat (x # M)"
  shows "sim_mat (obr_prve M)"
  using assms sim_mat.elims(2) by blast

  value "sim_mat (obr_prve [[True]])"
  value "sim_mat [[], []]"

fun dodaj_True ::"b_mat \<Rightarrow> b_mat" where
"dodaj_True [] = []"
| "dodaj_True (x # M) = (True # x) # dodaj_True M"

value "lista_b_n 1"

lemma prvi_True[simp]:
  assumes "jed M"
  shows "hd M = False # (lista_b_n (length M - 1))"
  sorry


lemma sabrani_true_pom[simp]:
  fixes M :: b_mat
  assumes "M \<noteq> []"
  assumes "sim_mat M"
  assumes "jed (gore_tr M)"
  shows " x \<in> set (partije_l M) \<longrightarrow> (Suc x = length M)"
  using assms
proof (induction M)
  case Nil
  show ?case
    by simp
next
  case (Cons m M)
  then have "set (Cons m M) = {m} \<union> set M"
    by simp
  from \<open>jed (gore_tr (Cons m M))\<close>
  have "m = False # lista_b_n (length m - 1)"
    by (metis gore_tr.simps(2) jed.simps(2)
        length_Cons list.sel(1) plus_1_eq_Suc prvi_True)
  from this have "m = False # (filter (\<lambda>x. x = False) m)"
    sorry
  show ?case sorry
qed

value "filter (\<lambda>x. x = 1) [1::nat,2,3]"

lemma sabrani_true[simp]:
  fixes M :: b_mat
  assumes "M \<noteq> []"
  assumes "sim_mat M"
  assumes "jed (gore_tr M)"
  shows "\<forall> x. x \<in> set (partije_l M) \<longrightarrow> (Suc x = length M)"
  using assms(1) assms(2) assms(3) sabrani_true_pom by blast

lemma skup_istih[simp]:
  fixes S :: "nat list"
  fixes m :: nat
  assumes "S \<noteq> []"
  assumes "\<forall> x. x \<in> set S \<longrightarrow> x = m"
  shows "set S = {m}"
proof -
  from `\<forall> x. x \<in> set S \<longrightarrow> x = m`
  have "x \<in> set S \<longrightarrow> x = m"
    by simp
  then show ?thesis
    using assms
  proof(induction S)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a S)
    then show ?case
      using assms
    proof (cases "S = []")
      case True
      then show ?thesis
      using Cons.prems(3) by auto
    next
      case False
     have "set (Cons a S) = {a} \<union> set S"
      by simp
    then have "S \<noteq> []"
    by (simp add: False)
    then have "set S \<subseteq> set (Cons a S)"
      by auto
    from this \<open>x \<in> set (Cons a S) \<longrightarrow> x = m\<close> have "x \<in> set S \<longrightarrow> x = m"
      by simp
    from this have "\<forall> x. x \<in> set S \<longrightarrow> x = m"
    by (simp add: Cons.prems(3))
  from this have "set S = {m}"
      using assms Cons
      using \<open>S \<noteq> []\<close> by blast
    then have "a \<in> set (Cons a S)"
      by simp
    from \<open>x \<in> set (Cons a S) \<longrightarrow> x = m\<close> \<open>a \<in> set (Cons a S)\<close>
    have "a = m"
      using Cons.prems(3) by blast
    from this `set (Cons a S) = {a} \<union> set S` `set S = {m}`show ?thesis
      by (simp add: \<open>a = m\<close> \<open>set S = {m}\<close>)
    qed
  qed
qed


fun rastuce :: "nat list \<Rightarrow> bool" where
"rastuce [] \<longleftrightarrow> True" |
"rastuce [x] \<longleftrightarrow> True" |
"rastuce (x # (y # l)) \<longleftrightarrow> (x < y) \<and> rastuce (y # l)"

lemma dodat_manji[simp]:
  assumes "sorted (a # l) \<and> (b < a)" 
  shows "sorted (b #(a # l))"
  using assms less_imp_le sorted2 by blast

lemma sortirani[simp]:
  assumes "rastuce l"
  shows "sorted l"
  using assms
proof (induction l)
  case Nil
  show ?case by simp
next
  case (Cons x l)
  show ?case
    using assms
  proof (cases "l = []")
    case True
    then show ?thesis
      by simp
  next
    case False
    then have "x < hd l"
      using assms
      using Cons.prems(1) rastuce.simps(3)
    by (metis list.exhaust_sel)
    then have "rastuce l"
      using Cons
    by (metis False list.exhaust_sel rastuce.simps(3))
    then have "sorted l"
      using assms Cons by simp
    from \<open>sorted l\<close> \<open>x < hd l\<close> show "sorted (x # l)"
    by (metis Cons.prems False dodat_manji neq_Nil_conv rastuce.simps(3))
  qed
qed


lemma rast_spajanje[simp]:
  assumes "rastuce l"
  assumes "(T > last l)"
  shows "rastuce (l @ [T])"
  using assms
proof(induction l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    using assms
  proof (cases "l = []")
    case True
    from `l = []` have "a # l = [a]"
      by simp
    from this have "last (a # l) = a"
      by simp
    from this assms(2) have "rastuce [a, T]"
    using Cons.prems(2) by auto
    from `a # l = [a]` have "[a, T] = (a # l) @ [T]"
      by simp
    from this `rastuce [a, T]` show ?thesis
      by simp
next
  case False
  from this have "length l \<ge> 1"
    by (simp add: Suc_le_eq)
  from this assms(2) have "rastuce (l @ [T])"
    using Cons
  proof -
    show ?thesis
      by (metis (no_types) Cons.IH False \<open>last (a # l) < T\<close> \<open>rastuce (a # l)\<close> last_ConsR rastuce.elims(3) rastuce.simps(3))
  qed
  from `length l \<ge> 1` have "l \<noteq> []"
  using False by blast
  from `rastuce (a # l)` `l \<noteq> []`  have " a < hd l"
    by (metis list.exhaust_sel rastuce.simps(3))
  from this have "rastuce ((a # l) @ [T])"
  by (metis False \<open>rastuce (l @ [T])\<close> append_Cons list.exhaust_sel rastuce.simps(3))
  from this show ?thesis
  by simp
qed
qed

lemma rast_spajanje2[simp]:
  assumes "rastuce l"
  assumes "T = Suc (last l)"
  shows "rastuce (l @ [T])"
  using assms(1) assms(2) rast_spajanje by blast



value "rev [0::nat, 1]"
value "sorted [1::nat,3]"
find_theorems name: "sorted"
value "1 \<le> hd (sort [2::nat, 1])"
value "sort [2::nat, 1]"

lemma obr_partije[simp]:
  assumes "length M > 1"
  assumes "sim_mat M"
  assumes "troug (gore_tr M)"
  shows "partije_l M =
  map (\<lambda>x. length M -1 - x) (partije_l (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) M))"
  sorry

lemma obr_partije2[simp]:
  assumes "length M > 1"
  assumes "sim_mat M"
  assumes "troug (gore_tr M)"
  shows "map (\<lambda>x. length M -1 - x) (partije_l M) =
  partije_l (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) M)"
  sorry


lemma poslednji_najveci[simp]:
  assumes "sorted l"
  shows "x \<in> set l \<longrightarrow> x \<le> last l"
  using assms
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  show ?case
    using assms
  proof (cases "l = []")
    case True
    then show ?thesis
      by simp
  next
    case False
from assms have "sorted (a # l)"
    using Cons.prems by blast
  from \<open>sorted (a # l)\<close> have "a \<le> hd l"
  by (simp add: False)
  from \<open>sorted (a # l)\<close> have "sorted l"
    by simp
  from this have "x \<in> set l \<longrightarrow> x \<le> last l"
    using Cons by simp
  from assms have "(l) \<noteq> []"
  by (simp add: False)
  from this have "hd l \<in> set l"
    by simp
  from this \<open>x \<in> set l \<longrightarrow> x \<le> last l\<close> have "hd l \<le> last l"
  by (metis \<open>sorted l\<close> eq_iff last_in_set list.exhaust_sel
      list.set_cases list.simps(3) set_ConsD sorted.simps(2))
  from this \<open>a \<le> hd l\<close> have "a \<le> last l"
    by simp
  then have "set (a # l) = {a} \<union> set l"
    by simp
  also have "last l = last (a # l)"
    using \<open>hd l \<in> set l\<close> by auto
  from this \<open>x \<in> set l \<longrightarrow> x \<le> last l\<close> have "x \<in> set l \<longrightarrow> x \<le> last (a # l)"
    by simp
  from \<open>last l = last (a # l)\<close> \<open>a \<le> last l\<close> have "a \<le> last (a # l)"
    by simp    
  then show ?thesis
  using \<open>x \<in> set l \<longrightarrow> x \<le> last (a # l)\<close>  by auto
  qed
qed

lemma dodato_rast[simp]:
  fixes T::nat
  assumes "rastuce l"
  shows "rastuce (map (\<lambda> x. x+T) l)"
  using assms
proof (induction l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    using assms
  proof (cases "l = []")
case True
  then show ?thesis
    by simp
next
  case False
  have "l \<noteq> []"
    by (simp add: False)
  from this `rastuce (a # l)` have "a < hd l"
    by (metis list.exhaust_sel rastuce.simps(3))
  from this have "a + T < hd l + T"
    by simp
  from assms have "rastuce (map (\<lambda> x. x+T) l)"
    using Cons
    by (metis rastuce.elims(3) rastuce.simps(3))
  from this `a + T < hd l + T`
  show ?thesis
    by (metis (no_types, lifting) False hd_map list.distinct(1)
        list.sel(1) list.sel(3) map_tl rastuce.elims(3))
  qed
qed

lemma dodat_posl[simp]:
  assumes "T \<ge> 1"
  assumes "rastuce l"
  shows "rastuce ( l @ [last l + T])"
  using assms
proof (induction l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
  proof (cases "l = []")
    case True
    from this have "last (Cons a l) = a"
      by simp
    then have "a < Suc a"
      by simp
    from this assms(1) have "a < a + T"
      by simp
    from this have "(Cons a l) @ [a+T] = [a, a+T]"
      by (simp add: True)
    from \<open>a < a + T\<close> have "rastuce [a, a+T]"
      by simp
    from this \<open>last (Cons a l) = a\<close>
    show ?thesis
    using \<open>(a # l) @ [a + T] = [a, a + T]\<close> by auto
next
  case False
  from this have "last l = last (a # l)"
    by simp
  then have "rastuce (l @ [last l +T])"
    using Cons
    by (metis rastuce.elims(3) rastuce.simps(3))
  from assms have "rastuce (a # l)"
    using Cons.prems(2) by blast
  from this have "a < hd l"
    by (metis False list.exhaust_sel rastuce.simps(3))
  from this \<open>rastuce (l @ [last l +T])\<close>
  show ?thesis
  by (metis False \<open>last l = last (a # l)\<close> append_Cons list.exhaust_sel rastuce.simps(3))
qed
qed


lemma oduzet_rast[simp]:
  assumes "rastuce l"
  shows "rastuce (rev (map (\<lambda> x. last l - x) l))"
  using assms
proof (induction l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    using assms
  proof (cases "l = []")
    case True
    then show ?thesis
      by simp
next
  case False
  from this have "a < hd l"
    by (metis Cons.prems list.exhaust_sel rastuce.simps(3))
  from \<open>rastuce (a # l)\<close> have "rastuce l"
    by (metis False list.exhaust_sel rastuce.simps(3))
  from \<open>rastuce (a # l)\<close> have "last l = last (a # l)"
    by (simp add: False)
  from this obtain T where "T = last l"
    by simp
  from this \<open>last l = last (a # l)\<close> have "T = last (a # l)"
    by simp
  from \<open>rastuce (a # l)\<close> \<open>T = last (a # l)\<close> have "T > a"
  by (metis False \<open>T = last l\<close> \<open>a < hd l\<close> \<open>rastuce l\<close>
      leD list.set_intros(1) list.set_sel(1) nat_less_le poslednji_najveci sortirani)
  from this have "T - a > 0"
    by simp
  from \<open>rastuce l\<close> \<open>T = last l\<close> have "T \<ge> hd l"
    using False hd_in_set poslednji_najveci sortirani by blast
  from this have "T - hd l \<ge> 0"
    by simp
  from this \<open>a < hd l\<close> \<open>T > a\<close> have "T - a > T - hd l"
    by simp
  then have "rastuce (rev (map (\<lambda> x. T - x) l))"
    using Cons \<open>T = last l\<close> \<open>rastuce l\<close> by blast
  from this obtain rev_l where "rev_l = rev (map (\<lambda> x. T - x) l)"
    by simp
  from this have "last rev_l = T - hd l"
    by (simp add: False hd_map last_rev)
  from \<open>rastuce (rev (map (\<lambda> x. T - x) l))\<close> have "rastuce rev_l"
  using \<open>rev_l = rev (map ((-) T) l)\<close> by blast
  from  \<open>T - a > T - hd l\<close>  have "(T - a) - (T - hd l) = hd l - a"
    using \<open>hd l \<le> T\<close> by auto
  from this have "(T - hd l) + (hd l - a) = T - a"
    using \<open>hd l \<le> T\<close> \<open>T - hd l < T - a\<close> by auto
  then have "hd l - a > 0"
  using \<open>a < hd l\<close> zero_less_diff by blast
  from this \<open>rastuce rev_l\<close> \<open>last rev_l = T - hd l\<close>
  have "rastuce (rev_l @ [(T-hd l) + (hd l - a)])"
    using dodat_posl
  by (metis One_nat_def less_eq_Suc_le)
  from this \<open>hd l \<le> T\<close> \<open>T - hd l < T - a\<close> have "rastuce (rev_l @ [T - a])"
    by simp
  from this show ?thesis
  by (simp add: \<open>T = last (a # l)\<close> \<open>rev_l = rev (map ((-) T) l)\<close>)
qed
qed


lemma poslednji_jedan[simp]:
  assumes "l \<noteq> []"
  assumes "rastuce l"
  assumes "last l = Tn"
  shows "filter (\<lambda> x. x = Tn) l = [Tn]"
  using assms
proof (induction l)
case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    using assms
  proof (cases "length (a # l) = 1")
    case True
    have "last (a # l) = Tn"
      using Cons.prems(3) by auto
    from `length (a # l) = 1` have "a # l = [a]"
      by simp
    from this have "last (a # l) = a"
      by simp
    from this `last (a # l) = Tn` have "a = Tn"
      by simp
    from this `a # l = [a]` have "filter (\<lambda> x. x =Tn) (a # l) = [Tn]"
      by simp
    then show ?thesis
      by simp
  next
    case False
    then have "length (a # l) > 1"
      by simp
    from this have "length l \<ge> 1"
      by (simp add: less_Suc_eq_le)
    from this have "length l > 0"
    by linarith
  from this `length l \<ge> 1 ` have "filter (\<lambda> x. x = last l)  l = [last l]"
    using Cons by (metis One_nat_def Suc_le_length_iff last_ConsR
        le_numeral_extra(2) list.size(3) rastuce.simps(3))
    from \<open>length l \<ge> 1\<close> obtain l_krace where "l = (hd l) # l_krace"
      by (metis One_nat_def less_Suc_eq_le less_irrefl list.exhaust_sel list.size(3))
    from this obtain Tn where "Tn = last l"
      by simp
    from `rastuce (a # l)` have "a < hd l"
      by (metis \<open>l = hd l # l_krace\<close> rastuce.simps(3))
    from `rastuce (a # l)` have "rastuce l"
      by (metis \<open>l = hd l # l_krace\<close> rastuce.simps(3))
    from this `rastuce l` have "sorted l"
      by simp
    from this have "hd l \<le> last l"
    by (metis \<open>l = hd l # l_krace\<close> hd_in_set list.simps(3) poslednji_najveci)
    from this `Tn = last l` have "hd l \<le> Tn"
    by simp
  from this `a < hd l` have "a < Tn"
    by simp
  from this have "a \<noteq> Tn"
    by simp
  from this `filter (\<lambda> x. x = last l)  l = [last l]` `Tn = last l`
  have "filter (\<lambda> x. x = Tn) (a # l) = [Tn]"
    by simp
  then show ?thesis
  using Cons.prems(3) \<open>Tn = last l\<close> by fastforce
  qed
qed


value "rastuce [3, 3, 1]"
value "(set [True, False]) = (set [False,True])"


lemma zadatak:
  assumes "n \<ge> 1"
  assumes "length t = n"
  assumes "rastuce t"
  assumes "hd t > 0"
  shows "\<exists> (p::b_mat). sim_mat p \<and> troug (gore_tr p) \<and>
  length p = 1 + last t \<and> (set t) = set (partije_l p)"
  using assms
proof (induction n)
  case 0
  thus ?case
    by simp
next
  case (Suc n)
  show ?case
    using assms
  proof (cases "n = 0")
    case True
    then have "Suc n = 1"
      using Suc
      by simp
    then have "length t = Suc n"
      using Suc assms(2)
      by simp
    from this `Suc n = 1` have "length t = 1"
      by simp
    from this have "\<exists> T. t = T#[]"
      by (metis One_nat_def Suc_length_conv length_0_conv)
    from this have "\<exists> T. t = [T]"
      by simp
    from this obtain T where "t = [T]"
      by blast
    then have "T = last t"
      by simp
    fix d
    assume "d = Suc (T)"
    have "d \<noteq> 0"
    by (simp add: \<open>d = Suc T\<close>)
    fix p
    assume "length p = d \<and> sim_mat p \<and> jed (gore_tr p)"
    then have "length p = d" "sim_mat p" "jed (gore_tr p)"
      by auto
    from `d = Suc (T)` have "d \<noteq> 0"
      by simp
    from this `length p = d` have "p \<noteq> []"
      by blast
    from this have "partije_l p \<noteq> []"
      by simp
    from this `sim_mat p` `jed (gore_tr p)`
    have "\<forall> x. x \<in> set (partije_l p) \<longrightarrow> Suc  x = (length p)"
      by simp
  from this have "\<forall> x. x \<in> set (partije_l p) \<longrightarrow> (x = d - 1)"
    by (metis \<open>length p = d\<close> diff_Suc_1)
  from this \<open>d = Suc T\<close> have "\<forall> x. x \<in> set (partije_l p) \<longrightarrow> (x = T)"
    by simp
  from \<open>length p = d\<close> have "length (partije_l p) = d"
    by simp
  from \<open>length (partije_l p) = d\<close> \<open>d \<noteq> 0\<close> have "partije_l p \<noteq> []"
    by blast
  from this \<open>\<forall> x. x \<in> set (partije_l p) \<longrightarrow> (x = T)\<close> have "set (partije_l p) = {T}"
    using skup_istih
  by blast
  then have "... = set t"
    using `t = [T]`
    by simp
  then have ?thesis
  by (metis \<open>T = last t\<close> \<open>d = Suc T\<close> \<open>jed (gore_tr p)\<close> \<open>length p = d\<close>
      \<open>set (partije_l p) = {T}\<close> \<open>sim_mat p\<close> jed.elims(2) plus_1_eq_Suc troug.simps(1) troug.simps(2))
next

    case False
    then have "Suc n \<ge> 2"
    using Suc
    by simp
  then have "length t = Suc n"
    using assms(2) Suc
    by simp
  from this have "length t \<noteq> 0"
    by simp
  from this have "t \<noteq> []"
    by simp
  from assms(3) have "rastuce t"
    by simp
  from this have "sorted t"
    by simp
  from this obtain Tn where "Tn = last t"
    by simp
  from this \<open>t \<noteq> []\<close> \<open>rastuce t\<close> have "filter (\<lambda> x. x = Tn) t = [Tn]"
    by simp
  then obtain t_nov where "t_nov = map (\<lambda> x. Tn - x) t"
    by blast
  from this have "last t_nov = 0"
  by (simp add: \<open>Tn = last t\<close> \<open>t \<noteq> []\<close> last_map)
  from \<open>t_nov = map (\<lambda> x. Tn - x) t\<close> have "length t = length t_nov"
    by simp
  from this `length t \<noteq> 0` have "length t_nov \<noteq> 0"
    by simp
  from this have "t_nov \<noteq> []"
    by simp
  from `sorted t` `Tn = last t`
  have "\<forall> x. x \<in> set t \<longrightarrow>  x \<le> Tn"
    by simp
  from this have "\<forall> x. x \<in> set t_nov \<longrightarrow> x \<ge> 0 \<and> x \<le> Tn"
    using \<open>t_nov = map ((-) Tn) t\<close> by auto
  from \<open>last t_nov = 0\<close> have "hd (rev t_nov) = 0"
    by (simp add: \<open>t_nov \<noteq> []\<close> hd_rev)
  from this `last t_nov = 0` obtain t_kraci where "t_kraci @ [0] = t_nov"
    using \<open>t_nov \<noteq> []\<close> append_butlast_last_id by fastforce
(*Treba ovde dodati korake da je pretposlednji iz t prvi u t_kraci i da je on manji od Tn pa Tn - hd t_kraci > 0*)
  from  this \<open>rastuce t\<close> \<open>t_nov = map (\<lambda> x. Tn - x) t\<close>
    \<open>\<forall> x. x \<in> set t_nov \<longrightarrow> x \<ge> 0 \<and> x \<le> Tn\<close>
  have "\<forall> x. x \<in> set t_kraci \<longrightarrow> x > 0 \<and> x \<le> Tn"
    sorry
  from this have "\<forall> x. x \<in> set t_kraci \<longrightarrow> x > 0"
    by simp
  from \<open>t_kraci @ [0] = t_nov\<close> have "0 # (rev t_kraci) = rev t_nov"
    by auto
  from `rastuce t` have "rastuce (rev t_nov)"
    using \<open>t_nov = map ((-) Tn) t\<close>
    by (simp add: \<open>Tn = last t\<close>)
  from this \<open>0 # (rev t_kraci) = rev t_nov\<close> have "0 < hd (rev t_kraci)"
  by (metis False Suc.prems(2) Suc_inject \<open>length t = length t_nov\<close>
length_Cons length_rev list.exhaust_sel list.size(3) rastuce.simps(3))
  from \<open>rastuce (rev t_nov)\<close> have "rastuce (rev t_kraci)"
  by (metis \<open>0 # rev t_kraci = rev t_nov\<close> rastuce.elims(3) rastuce.simps(3))
  from `0 # (rev t_kraci) = rev t_nov` have "Suc (length (rev t_kraci)) = length t_nov"
  using \<open>t_kraci @ [0] = t_nov\<close> by auto
  then have "length (rev t_kraci) > 0"
  using False Suc.prems(2) \<open>length t = length t_nov\<close> by linarith
  from \<open>Suc (length (rev t_kraci)) = length t_nov\<close> \<open>length t = length t_nov\<close>
  have "length (rev t_kraci) + 1 = length t"
    by simp
  from this have "length t = Suc (length (rev t_kraci))"
    by simp
  from assms(2) have "length t = Suc n"
  using Suc.prems(2) by blast
  from this \<open>length t = Suc (length (rev t_kraci))\<close> have "n = length (rev t_kraci)"
   by linarith
  from this obtain rev_kraci where "rev_kraci = rev t_kraci"
    by simp
  from this \<open>rastuce (rev t_kraci)\<close> have "rastuce rev_kraci"
    by simp
  from\<open>rev_kraci = rev t_kraci\<close> \<open>length (rev t_kraci) > 0\<close> have "length (rev_kraci) > 0"
    by simp
  from this have "1 \<le> length (rev_kraci)"
    by linarith
  from this \<open>n = length (rev t_kraci)\<close> \<open>rev_kraci = rev t_kraci\<close> have "n = length rev_kraci"
    by simp
  from \<open>rastuce (rev t_kraci)\<close> \<open>rev_kraci = rev t_kraci\<close> have "rastuce rev_kraci"
    by simp
  from \<open>0 < hd (rev t_kraci)\<close> \<open>rev_kraci = rev t_kraci\<close> have "0 < hd rev_kraci"
    by simp
  from \<open>Suc n \<ge> 2\<close> have "1 \<le> n"
    by simp
  from assms \<open>1 \<le> n\<close> \<open>0 < hd rev_kraci\<close> \<open>rastuce rev_kraci\<close> \<open>n = length rev_kraci\<close>
  have "\<exists> (p::b_mat). sim_mat p \<and> troug (gore_tr p)
  \<and> length p = 1 + last rev_kraci \<and> (set rev_kraci) = set (partije_l p)"
    using Suc sorry
  from this obtain p_kraca where "sim_mat p_kraca \<and> troug (gore_tr p_kraca) \<and>
  length p_kraca = 1 + last (rev_kraci) \<and> (set (rev_kraci)) = set (partije_l p_kraca)"
    by blast
  from this have "troug (gore_tr p_kraca)"
    by simp
  from \<open>sim_mat p_kraca \<and> troug (gore_tr p_kraca) \<and>
  length p_kraca = 1 + last (rev_kraci) \<and> (set (rev_kraci)) = set (partije_l p_kraca)\<close>
    \<open>rev_kraci = rev t_kraci\<close> have "length p_kraca = 1 + last (rev (t_kraci))"
    by simp
  from this have "length p_kraca = 1 + hd t_kraci"
    using False \<open>n = length rev_kraci\<close> \<open>rev_kraci = rev t_kraci\<close> last_rev by auto
  from this \<open>t_kraci @ [0] = t_nov\<close> have "length p_kraca = 1 + hd t_nov"
    using False \<open>n = length rev_kraci\<close> \<open>rev_kraci = rev t_kraci\<close> by auto
  from this \<open>t_nov = map (\<lambda> x. Tn - x) t\<close> have "length p_kraca = 1 + (Tn - hd t)"
    by (simp add: \<open>t \<noteq> []\<close> hd_map)
  from \<open>sim_mat p_kraca \<and> troug (gore_tr p_kraca) \<and>
  length p_kraca = 1 + last (rev_kraci) \<and> (set (rev_kraci)) = set (partije_l p_kraca)\<close>
  have "length p_kraca = 1 + last(rev_kraci)"
    by simp
  from this \<open>length t = Suc (length (rev t_kraci))\<close> \<open>length t = Suc n\<close> \<open>rev_kraci = rev (t_kraci)\<close>
  have "Suc n = Suc (length rev_kraci)"
    by simp
  from \<open>t_nov = map (\<lambda> x. Tn - x) t\<close> have "hd t_nov = Tn - hd t"
    using \<open>t \<noteq> []\<close> hd_map by blast
  from this \<open>t_kraci @ [0] = t_nov\<close>  have "Tn - hd t_kraci = Tn - hd t_nov"
    using False \<open>n = length (rev t_kraci)\<close> by auto
  from \<open>rev_kraci = rev t_kraci\<close> have "hd t_kraci = last rev_kraci"
    using False \<open>n = length (rev t_kraci)\<close> last_rev by force
  from this \<open>Tn - hd t_kraci =Tn - hd t_nov\<close> have "Tn - (last rev_kraci) = Tn - hd t_nov"
    by simp
  from this \<open>hd t_nov = Tn - hd t\<close> have "Tn - last rev_kraci = Tn - (Tn - hd t)"
    by simp
  from this have "Tn - last rev_kraci = Tn - Tn + hd t"
    by (simp add: \<open>Tn = last t\<close> \<open>t \<noteq> []\<close> assms(3))
  from this have "Tn - last rev_kraci = hd t"
    by simp
  fix t_krajnji
  assume "t_krajnji = (rev_kraci) @ [Tn]"
  from this have "length t_krajnji = length rev_kraci + 1"
    by simp
  from this  have "length t_krajnji = length t_kraci + 1"
    by (simp add: \<open>rev_kraci = rev t_kraci\<close>)
  from this have "length t_krajnji = Suc n"
  using Suc.prems(2) \<open>length (rev t_kraci) + 1 = length t\<close>
    by auto
  from \<open>hd t > 0\<close> \<open>Tn - last rev_kraci = hd t\<close> have "Tn > last rev_kraci"
  by linarith
  from \<open>rastuce (rev_kraci)\<close> \<open>Tn > last rev_kraci\<close>
  have  "rastuce ((rev_kraci) @ [Tn])"
    using rast_spajanje by blast
  from \<open>sim_mat p_kraca \<and> troug (gore_tr p_kraca) \<and>
  length p_kraca = 1 + last (rev_kraci) \<and> (set (rev_kraci)) = set (partije_l p_kraca)\<close>
    \<open>rev_kraci = rev t_kraci\<close>
  have "sim_mat p_kraca"
    by simp
  from this have "sim_mat (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) p_kraca)"
    sorry
  from this obtain pom where "pom =  (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) p_kraca)"
    by simp
  from this
  have "gore_tr pom = (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) (gore_tr p_kraca))"
    sorry
  from this \<open>troug (gore_tr p_kraca)\<close>
  have "troug (gore_tr pom)"
    by simp
  from this obtain obr where "obr = gore_tr pom"
    by simp
  from this \<open>gore_tr pom = (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) (gore_tr p_kraca))\<close>
  have "obr =  (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) (gore_tr p_kraca))"
    by simp
  from this \<open>troug (gore_tr pom)\<close>
  have "troug (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) (gore_tr p_kraca))"
  
  by (simp add: \<open>gore_tr pom = map (\<lambda>red. hd red # map Not (tl red)) (gore_tr p_kraca)\<close>)
  from \<open>obr =  (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) (gore_tr p_kraca))\<close>
\<open>length p_kraca = 1 + (Tn - hd t)\<close> have "length obr = 1 + Tn - hd t"
    by (smt Nat.add_diff_assoc \<open>Tn - last rev_kraci = hd t\<close>
    \<open>sim_mat p_kraca \<and> troug (gore_tr p_kraca) \<and> length p_kraca = 1 + last rev_kraci \<and> set rev_kraci = set (partije_l p_kraca)\<close>
  diff_le_self gore_tr.elims length_0_conv length_Cons length_map list.inject nat.simps(3)
  plus_1_eq_Suc sim_mat.elims(2) troug.elims(2))
  from \<open>obr = map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) (gore_tr p_kraca)\<close>
    \<open>troug (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) (gore_tr p_kraca))\<close>
  have "troug obr"
    by simp
  from this have "troug (dop_do_jed (hd t) obr)"
  using trug_dop by blast
  from \<open>obr = map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) (gore_tr p_kraca)\<close>
  have "length obr = length p_kraca"
  using \<open>Tn - last rev_kraci = hd t\<close> \<open>length obr = 1 + Tn - hd t\<close>
    \<open>length p_kraca = 1 + (Tn - hd t)\<close> by linarith
  from this  have "length (dop_do_jed (hd t) obr) = length p_kraca + hd t"
  by (simp add: assms(4))  
    obtain mat_krajnja where "mat_krajnja = troug_u_sim (dop_do_jed (hd t) obr)"
    by simp
  from this have "sim_mat mat_krajnja"
    by (simp add: \<open>troug (dop_do_jed (hd t) obr)\<close>)
  from \<open>mat_krajnja = troug_u_sim (dop_do_jed (hd t) obr)\<close>
  have "length mat_krajnja = length (dop_do_jed (hd t) obr)"
  by (smt \<open>sim_mat mat_krajnja\<close> \<open>troug (dop_do_jed (hd t) obr)\<close> length_Cons
  list.inject null_rec(1) null_rec(2) plus_1_eq_Suc sim_mat.elims(2) troug.elims(2) troug_u_sim.elims)
  from this \<open>length (dop_do_jed (hd t) obr) = length p_kraca + hd t\<close>
  have "length (dop_do_jed (hd t) obr) = length p_kraca + hd t"
    by simp
  from this \<open>length mat_krajnja = length (dop_do_jed (hd t) obr)\<close>
  have "length mat_krajnja = length p_kraca + hd t"
  by (simp add: \<open>length (dop_do_jed (hd t) obr) = length p_kraca + hd t\<close>
\<open>length mat_krajnja = length (dop_do_jed (hd t) obr)\<close>)
  from this \<open>length p_kraca = 1 + (Tn - hd t)\<close> have "length mat_krajnja = 1 + Tn - (hd t) + (hd t)"
    using \<open>length obr = 1 + Tn - hd t\<close> \<open>length obr = length p_kraca\<close> by linarith
  from this have "length mat_krajnja = 1 + Tn"
  using \<open>length obr = 1 + Tn - hd t\<close> \<open>length obr = length p_kraca\<close>
    \<open>length p_kraca = 1 + (Tn - hd t)\<close> by linarith
  from \<open>length obr = 1 + Tn - hd t\<close> \<open>mat_krajnja = troug_u_sim (dop_do_jed (hd t) obr)\<close>
  have "partije_l mat_krajnja =
  (map (\<lambda> x. x + (hd t))(partije_l (troug_u_sim obr))) @ (lista_nat_n (length obr + (hd t) - 1) (hd t))"
  by (metis \<open>length obr = length p_kraca\<close> \<open>length p_kraca = 1 + hd t_kraci\<close> \<open>troug obr\<close> assms(4)
length_0_conv length_greater_0_conv nat.simps(3) parije_dodate plus_1_eq_Suc)
  from this \<open>length obr = 1 + Tn - hd t\<close>
  have "partije_l mat_krajnja =
  (map (\<lambda> x. x + (hd t))(partije_l (troug_u_sim obr))) @ (lista_nat_n (1 + Tn  - hd t + (hd t) - 1) (hd t))"
    by simp
  from this have "partije_l mat_krajnja =
  (map (\<lambda> x. x + (hd t))(partije_l (troug_u_sim obr))) @ (lista_nat_n (Tn) (hd t))"
    using \<open>length mat_krajnja = 1 + Tn - hd t + hd t\<close> \<open>length mat_krajnja = 1 + Tn\<close> by auto
  from this obtain krajnje_partije where "krajnje_partije = partije_l mat_krajnja"
    by simp
  from this \<open>partije_l mat_krajnja =
  (map (\<lambda> x. x + (hd t))(partije_l (troug_u_sim obr))) @ (lista_nat_n (Tn) (hd t))\<close>
  have "krajnje_partije = (map (\<lambda> x. x + (hd t))(partije_l (troug_u_sim obr))) @ (lista_nat_n (Tn) (hd t))"
    by simp
  from this have "set (partije_l mat_krajnja) =
  set (map (\<lambda> x. x + (hd t))(partije_l (troug_u_sim obr))) \<union> set (lista_nat_n (Tn) (hd t))"
    using List.set_append \<open>krajnje_partije = partije_l mat_krajnja\<close> by auto
  from \<open>0 < hd t\<close> have "set (lista_nat_n (Tn) (hd t)) = {Tn}"
    by simp
  from this \<open>Tn = last t\<close> have "... \<subseteq> set (t)"
  by (meson \<open>t \<noteq> []\<close> empty_subsetI insert_subset last_in_set)
  from \<open>troug obr\<close>
  have "sim_mat (troug_u_sim obr)"
    by simp
  from \<open>pom = (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) p_kraca)\<close>
    \<open>sim_mat (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) p_kraca)\<close>
  have "sim_mat pom"
    by simp
  from \<open>sim_mat pom\<close> \<open>troug (gore_tr pom)\<close> \<open>obr = gore_tr pom\<close> have "troug_u_sim (gore_tr pom) = pom"
  using \<open>pom = map (\<lambda>red. hd red # map Not (tl red)) p_kraca\<close>
    \<open>sim_mat (map (\<lambda>red. hd red # map Not (tl red)) p_kraca)\<close> \<open>troug (gore_tr pom)\<close>
    mat_tr_sim by presburger
  from this \<open>obr = gore_tr pom\<close> have "troug_u_sim obr = pom"
    by simp
  from \<open>set (partije_l mat_krajnja) =
  set (map (\<lambda> x. x + (hd t))(partije_l (troug_u_sim obr))) \<union> set (lista_nat_n (Tn) (hd t))\<close>
  \<open>set (lista_nat_n (Tn) (hd t)) = {Tn}\<close>
  have "set (partije_l mat_krajnja) =  set (map (\<lambda> x. x + (hd t))(partije_l (troug_u_sim obr))) \<union> {Tn}"
    by simp
  from this \<open>troug_u_sim obr = pom\<close>
  have "set (partije_l mat_krajnja) = set (map (\<lambda> x. x + (hd t)) (partije_l pom)) \<union> {Tn}"
    by simp
  from this \<open>pom = (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) p_kraca)\<close>
  have "set (partije_l mat_krajnja) = set (map (\<lambda> x. x + (hd t))
  (partije_l (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) p_kraca))) \<union> {Tn}"
    by simp
  from \<open>length p_kraca =  1 + last (rev_kraci)\<close>
  have "length p_kraca > 1"
  by (metis One_nat_def Suc_less_eq \<open>0 < hd (rev t_kraci)\<close>
      \<open>0 < length (rev t_kraci)\<close> \<open>rastuce (rev t_kraci)\<close>
  \<open>rev_kraci = rev t_kraci\<close> gr_zeroI hd_in_set leD length_greater_0_conv
  plus_1_eq_Suc poslednji_najveci sortirani)
  from this \<open>sim_mat p_kraca\<close> \<open>troug (gore_tr p_kraca)\<close>
  have "partije_l (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) p_kraca)
  = map (\<lambda> x. length p_kraca -1 - x) (partije_l p_kraca)"
    using obr_partije2  by presburger
  from this \<open>set (partije_l mat_krajnja) = set (map (\<lambda> x. x + (hd t))
  (partije_l (map (\<lambda> red. hd red # map (\<lambda> el. \<not> el) (tl red)) p_kraca))) \<union> {Tn}\<close>
  have "set (partije_l mat_krajnja) = set (map (\<lambda> x. x + (hd t))
  (map (\<lambda> x. length p_kraca -1 - x)(partije_l p_kraca))) \<union> {Tn}"
    by simp
  from \<open>sim_mat p_kraca \<and> troug (gore_tr p_kraca) \<and>
  length p_kraca = 1 + last (rev_kraci) \<and> (set (rev_kraci)) = set (partije_l p_kraca)\<close>
  have "set (rev_kraci) = set (partije_l p_kraca)"
    by simp
  from \<open>sim_mat p_kraca \<and> troug (gore_tr p_kraca) \<and>
  length p_kraca = 1 + last (rev_kraci) \<and> (set (rev_kraci)) = set (partije_l p_kraca)\<close>
  have "length p_kraca = 1 + last (rev_kraci)"
    by simp
  from this \<open>hd t_kraci = last rev_kraci\<close> have "length p_kraca = 1 + hd t_kraci"
    by simp
  from \<open>t_kraci @ [0] = t_nov\<close> have "hd t_kraci = hd t_nov"
    using False \<open>n = length rev_kraci\<close> \<open>rev_kraci = rev t_kraci\<close> by auto
  from this \<open>length p_kraca = 1 + hd t_kraci\<close> have "length p_kraca = 1 + hd t_nov"
    by simp
  from this \<open>t_nov = map (\<lambda> x. Tn - x) t\<close> have "length p_kraca = 1 + Tn - hd t"
    using \<open>length obr = 1 + Tn - hd t\<close> \<open>length obr = length p_kraca\<close> by linarith
  from this \<open>set (partije_l mat_krajnja) = set (map (\<lambda> x. x + (hd t))
  (map (\<lambda> x. length p_kraca -1 - x)(partije_l p_kraca))) \<union> {Tn}\<close>
  have "set (partije_l mat_krajnja) = set (map (\<lambda> x. x + (hd t))
  (map (\<lambda> x. 1 + Tn -1 - hd t - x)(partije_l p_kraca))) \<union> {Tn}"
    by simp
  from this have "set (partije_l mat_krajnja) =
set (map ((\<lambda> x. x + (hd t)) \<circ> (\<lambda> x. 1 + Tn -1 - hd t - x))(partije_l p_kraca)) \<union> {Tn}"
    by simp
  from this have "set (partije_l mat_krajnja) =
  set (map (\<lambda> x. 1 + Tn -1 - (hd t) - x + (hd t))(partije_l p_kraca)) \<union> {Tn}"
    by simp
  from this have "set (partije_l mat_krajnja) =
  set (map (\<lambda> x. Tn - (hd t) - x + (hd t))(partije_l p_kraca)) \<union> {Tn}"
    by simp
  from this \<open>hd t > 0\<close> have "set (partije_l mat_krajnja) =
  set (map (\<lambda> x. Tn - x)(partije_l p_kraca)) \<union> {Tn}"
    sorry
  from \<open>sim_mat p_kraca \<and> troug (gore_tr p_kraca) \<and>
  length p_kraca = 1 + last (rev_kraci) \<and> (set (rev_kraci)) = set (partije_l p_kraca)\<close>
  have "(set (rev_kraci)) = set (partije_l p_kraca)"
    by simp
  from this have "set (map (\<lambda> x. Tn - x) rev_kraci) =
  set (map (\<lambda> x. Tn - x) (partije_l p_kraca))"
    by auto
  from this \<open>set (partije_l mat_krajnja) =
  set (map (\<lambda> x. Tn - x)(partije_l p_kraca)) \<union> {Tn}\<close>
  have "set (partije_l mat_krajnja) =
  set (map (\<lambda> x. Tn - x) rev_kraci) \<union> {Tn}"
    by simp
  from this \<open>rev_kraci = rev t_kraci\<close> have "set (partije_l mat_krajnja) =
  set (map (\<lambda> x. Tn - x) (rev t_kraci)) \<union> {Tn}"
    by simp
  from this have "set (partije_l mat_krajnja) =
  set (map (\<lambda> x. Tn - x) t_kraci) \<union> {Tn}"
    by simp
  from \<open>t_kraci @ [0] = t_nov\<close> have
 "(set (map (\<lambda> x. Tn - x) (t_kraci @ [0]))) =
  (set (map (\<lambda> x. Tn - x) t_nov))"
    by simp
  from this have "(set (map (\<lambda> x. Tn - x) (t_kraci))) \<union> set (map  (\<lambda> x. Tn - x) [0]) =
   (set (map (\<lambda> x. Tn - x) t_nov))"
    by simp
  from this \<open>\<forall> x. x \<in> set t_kraci \<longrightarrow> x > 0\<close>
  have "(set (map (\<lambda> x. Tn - x) (t_kraci))) =
   (set (map (\<lambda> x. Tn - x) t_nov)) - set (map  (\<lambda> x. Tn - x) [0])"
    sorry
  from this have "(set (map (\<lambda> x. Tn - x) (t_kraci))) =
   (set (map (\<lambda> x. Tn - x) t_nov)) - set ([Tn])"
    by simp
  from this have "(set (map (\<lambda> x. Tn - x) (t_kraci))) =
   (set (map (\<lambda> x. Tn - x) t_nov)) - {Tn}"
    by simp
  from this \<open>set (partije_l mat_krajnja) =
  set (map (\<lambda> x. Tn - x) t_kraci) \<union> {Tn}\<close>
  have "set (partije_l mat_krajnja) = ((set (map (\<lambda> x. Tn - x) t_nov)) - {Tn}) \<union> {Tn}"
    by simp
  from this have "set (partije_l mat_krajnja) = set (map (\<lambda> x. Tn - x) t_nov)"
    using \<open>set (map ((-) Tn) t_kraci) \<union> set (map ((-) Tn) [0]) = set (map ((-) Tn) t_nov)\<close> by auto
  from this \<open>t_nov = map (\<lambda> x. Tn - x) t\<close>
  have "set (partije_l mat_krajnja) = set (map (\<lambda> x. Tn - x) (map (\<lambda> x. Tn - x) t))"
    by simp
  from this have "set (partije_l mat_krajnja) = set (map ((\<lambda> x. Tn - x)\<circ>(\<lambda> x. Tn - x)) t)"
    by simp
  from this have "set (partije_l mat_krajnja) = set (map (\<lambda>x. Tn - (Tn - x)) t)"
    by simp
  from this have "set (partije_l mat_krajnja) = set (map (\<lambda> x. Tn - Tn + x) t)"
  by (simp add: \<open>\<forall>x. x \<in> set t \<longrightarrow> x \<le> Tn\<close> cancel_comm_monoid_add_class.diff_cancel
      diff_diff_cancel map_idI)
  from this have "set (partije_l mat_krajnja) = set (map (\<lambda> x. x) t)"
    by simp
  from this have "set (partije_l mat_krajnja) = set t"
    by simp
  from \<open>mat_krajnja = troug_u_sim (dop_do_jed (hd t) obr)\<close> \<open>troug ((dop_do_jed (hd t) obr))\<close>
  have "gore_tr mat_krajnja = dop_do_jed (hd t) obr"
    by simp
  from this \<open>troug (dop_do_jed (hd t) obr)\<close> have "troug (gore_tr mat_krajnja)"
    by simp
  from \<open>set (partije_l mat_krajnja) = set t\<close> \<open>length mat_krajnja = 1 + Tn\<close>
    \<open>Tn = last t\<close> \<open>sim_mat mat_krajnja\<close>
    \<open>troug (gore_tr mat_krajnja)\<close> show ?thesis
    
  qed
qed

find_theorems "set (_ @ _)"
find_theorems "map _ (map _ _)"

end