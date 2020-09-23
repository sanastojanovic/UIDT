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
"b_kv a = (size_list length a =(length a)*(1+length a))"

value "b_kv [[True, False], [True, True]]"

(*Funkcija prvi vraca prvi element bool liste.*)

fun prvi :: "bool list \<Rightarrow> bool" where
"prvi [] = False"
|"prvi (x # l) = x"

value "prvi [True, False, True]"

(*Funkcija partije_l od bool matrice pravi listu koja čuva koliko je svaki igrač odigrao partija.*)

fun partije_l :: "b_mat \<Rightarrow> nat list" where
"partije_l M = map (\<lambda> x. sum_list (map (\<lambda>x. If (x=True) 1 0) x)) M"

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

value "gore_tr [[True, False, True], [False, True, False], [False, False, True]]"

(*Funkcija koja vraca da li je matrica trougaona, sa glavnom dijagonalom false.*)

fun troug :: "b_mat \<Rightarrow> bool" where
"troug [] \<longleftrightarrow> True"
|"troug (Cons x l) \<longleftrightarrow> (troug l) \<and> (1 + length l = length x) \<and> (\<not> prvi x)"


(*Provera da li ispravno radi trougaona matrica.*)
value "troug [[False, True, True],[False, True], [False]]"
value "size_list length [[],[[]]]"

(*Lema fiksira n i listu od t1 do tn. Pokazuje da postoji takva trougaona bool matrica p,
sa False na glavnoj dijagonali, za koju istovremeno mogu da važe uslovi (i) i (ii) iz zadatka.*)

(*Funkcija pocetni izdvaja sve pocetne elemente redova bool matrice u bool listu.*)

fun pocetni :: "b_mat \<Rightarrow> b_list" where
"pocetni [] = []"
| "pocetni (x # l) = (prvi x) # (pocetni l)"

value "pocetni [[True, False],[True, False],[]]"

value "size_list length[[True,False,True],[True,True,False],[False,False,False]]"


(*Provera da li je matrica simetricna: Direktno proveriti u jednoj funkciji, tako sto se
proverava da li je simetricna matrica kojoj se obrise prva kolona i prvi red i a li su prva kolona i
prvi red jednaki, a onda rekurzivno to primeniti da ostatak matrice.*)
(*Funkcija sim_mat*)

function sim_mat :: "b_mat \<Rightarrow> bool" where
"sim_mat [] \<longleftrightarrow> True"
| "sim_mat ([] # l) \<longleftrightarrow> False"
| "sim_mat ((x # y) # l) \<longleftrightarrow> b_kv (obr_prve l) \<and> (length y = length l) \<and> (y = (pocetni l)) \<and> sim_mat (obr_prve l) "
  by pat_completeness auto
termination 
  apply (relation "measure (\<lambda> m. length m)")
   apply auto
  done

value "sim_mat [[True, True, False], [True, False, False], [False, False, False]]"
value " troug (gore_tr [[True, True, False], [True, False, False], [False, False, False]])"
value " troug (gore_tr [[False, True, False], [True, False, False], [False, False, False]])"

fun sve_true :: "b_list \<Rightarrow> bool" where
"sve_true [] \<longleftrightarrow> True" |
"sve_true (Cons x xs) \<longleftrightarrow> x \<and> (sve_true xs)"

value "sve_true [True, True, False]"

fun jed :: "b_mat \<Rightarrow> bool" where
"jed [] \<longleftrightarrow> True" |
"jed (Cons x l) \<longleftrightarrow> (troug l) \<and> (1 + length l = length x) \<and> (\<not> prvi x) \<and> (sve_true (bez_pr x)) \<and> jed l"

value "jed [[False, True, True], [False, True], [False]]"
value "troug [[False, True, True], [False, False], [False]]"

lemma sabrani_true[simp]:
  fixes M :: b_mat
  assumes "M \<noteq> []"
  assumes "sim_mat M"
  assumes "jed (gore_tr M)"
  shows "\<forall> x. x \<in> set (partije_l M) \<longrightarrow> (Suc x = length M)"
(*proof (induction M)
  case Nil
  show ?case
    by simp
next
  case (Cons m M)
  then have "set (Cons m M) = {m} \<union> set M"
    by simp
  then have "(\<forall> x. x \<in> set (Cons m M) \<longrightarrow> (Suc (sum_list (map (\<lambda> x. If (x = True) 1 0) x)) = length (Cons m M)))
             \<longleftrightarrow> (\<forall> x. x \<in> {m} \<union> set M \<longrightarrow> (Suc (sum_list (map (\<lambda> x. If (x = True) 1 0) x)) = length (Cons m M)))"
    by simp
  then have "... \<longleftrightarrow> ((x = m) \<longrightarrow>  (Suc (sum_list (map (\<lambda> x. If (x = True) 1 0) x)) = length (Cons m M))
                     \<and> (\<forall> x. x \<in> set M) \<longrightarrow>  (Suc (sum_list (map (\<lambda> x. If (x = True) 1 0) x)) = length M))"
    sorry
qed*)
  sorry

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
  assumes "rastuce l1"
  assumes "rastuce l2"
  shows "rastuce (l1 @ l2)"
  sorry

value "rev [0::nat, 1]"
value "sorted [1::nat,3]"
find_theorems name: "sorted"
value "take 1 [0::nat, 1]"
value "1 \<le> hd (sort [2::nat, 1])"
value "sort [2::nat, 1]"

thm sorted_append
find_theorems "sorted (_ # _)"

find_theorems "hd _ \<in> set _"


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
  using \<open>x \<in> set l \<longrightarrow> x \<le> last (a # l)\<close> by auto
    
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
    from this `Tn = last l` have "hd l \<le> Tn"
    by (metis \<open>1 \<le> length l\<close> le_cases le_numeral_extra(2)
        list.inject list.set_sel(1) list.size(3) not_le nth_Cons_0 poslednji_najveci)
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
  fixes n::nat and t::"nat list"
  assumes "n \<ge> 1"
  assumes "length t = n"
  assumes "rastuce t"
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

  from this have "0 # (rev t_kraci) = rev t_nov"
    by auto
  from `rastuce t` have "rastuce (rev t_nov)"
    using \<open>t_nov = map ((-) Tn) t\<close>
  by (simp add: rev_induct)
  from this have "rastuce (rev t_kraci)"
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
  from this assms \<open>rastuce (rev t_kraci)\<close> \<open>length (rev t_kraci) > 0\<close>
  have "\<exists> (p_kraca::b_mat). sim_mat p_kraca \<and> troug (gore_tr p_kraca)
  \<and> length p_kraca = 1 + last (rev t_kraci) \<and> (set (rev t_kraci)) = set (partije_l p_kraca)"
    using Suc(1) diff_Suc \<open>length t = Suc (length (rev t_kraci))\<close>
    by (metis One_nat_def \<open>0 # rev t_kraci = rev t_nov\<close> \<open>rastuce (rev t_nov)\<close> add.right_neutral
add_Suc_right append.simps(1) append.simps(2) leD lessI linorder_not_less list.simps(3)
order_refl rast_spajanje rastuce.elims(3) rastuce.simps(3) rev_append rev_singleton_conv
upt_eq_Cons_conv upt_eq_Nil_conv zero_less_Suc zero_order(3))
 
  from this obtain p_kraca where "sim_mat p_kraca \<and> troug (gore_tr p_kraca) \<and>
  length p_kraca = 1 + last (rev t_kraci) \<and> (set (rev t_kraci)) = set (partije_l p_kraca)"
    by blast
  fix t_krajnji
  assume "t_krajnji = sort ([((last (rev t_kraci))+1)] @ (rev t_kraci))"
  from this have "sorted t_krajnji"
  using sorted_sort by blast
  then have "(last (rev t_kraci)) + 1 > last (rev t_kraci)"
    by simp
  from this \<open>sorted t_krajnji\<close> \<open>rastuce (rev t_kraci)\<close>
  have "rastuce t_krajnji"
  by (metis \<open>0 # rev t_kraci = rev t_nov\<close> bez_pr.simps(2) list.simps(3) rast_spajanje
rastuce.elims(3) rastuce.simps(3) rev.simps(2) rev_append rev_rev_ident rev_singleton_conv zero_order(3))
 
  qed
qed


end