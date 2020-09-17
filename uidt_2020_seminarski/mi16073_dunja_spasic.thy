theory mi16073_dunja_spasic
  imports Main

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
  assumes "sim_mat M"
  assumes "jed (gore_tr M)"
  shows "\<forall> x. x \<in> set M \<longrightarrow> (Suc (sum_list (map (\<lambda> x. If (x = True) 1 0) x)) = length M)"
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
  assumes "\<forall> x. x \<in> set S \<longrightarrow> x = m"
  shows "s = {m}"
  sorry


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
  note ih = \<open>rastuce l \<Longrightarrow> sorted l\<close>
  then show ?case
    using assms
  proof (induction l)
    case Nil
    show ?case
      by simp
  next
    case (Cons y l)
    have "x < y"
      using assms
      using Cons.prems(1) rastuce.simps(3) by blast
    then have "rastuce (y # l)"
      using Cons.prems(1) rastuce.simps(3) by blast
    then have "sorted (y # l)"
      using assms Cons ih by simp
    from \<open>sorted (y # l)\<close> \<open>x < y\<close> show "sorted (x # (y # l))"
      by (metis dodat_manji)
  qed
qed

lemma poslednji_najveci[simp]:
  assumes "sorted l"
  shows "x \<in> set l \<longrightarrow> x \<le> last l"
  sorry

value "rastuce [3, 3, 1]"
value "(set [True, False]) = (set [False,True])"


lemma
  fixes n::nat and t::"nat list"
  assumes "n \<ge> 1"
  assumes "length t = n"
  assumes "rastuce t"
  assumes "True"
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
    fix p
    assume "length p = d \<and> sim_mat p \<and> jed (gore_tr p)"
    then have "length p = d" "sim_mat p" "jed (gore_tr p)"
      by auto
    from `sim_mat p` `jed (gore_tr p)`
    have "\<forall> x. x \<in> set p \<longrightarrow> sum_list (map (\<lambda> x. If (x = True) 1 0) (last p)) = (length p) - 1"
      by (metis diff_Suc_1 last_in_set length_greater_0_conv length_pos_if_in_set sabrani_true)
    from this have "\<forall> x. x \<in> set (partije_l p) \<longrightarrow> (x = (length p) - 1)"
    using \<open>jed (gore_tr p)\<close> \<open>sim_mat p\<close> sabrani_true
    by fastforce
  from this have "\<forall> x. x \<in> set (partije_l p) \<longrightarrow> (x = d - 1)"
  using \<open>length p = d\<close>
  by blast
  from this have "\<forall> x. x \<in> set (partije_l p) \<longrightarrow> (x = T)"
    using `d = Suc (T)`
    by simp
  from this have "set (partije_l p) = {T}"
    using skup_istih
    by blast
  then have "... = set t"
    using `t = [T]`
    by simp
  then have ?thesis
    by (metis empty_iff insertCI list.set(1) skup_istih)

next

    case False
    then have "Suc n \<ge> 2"
    using Suc
    by simp
  then have "length t = Suc n"
    using assms(2) Suc
    by simp
  from assms(3) have "rastuce t"
    by simp
  from this have "sorted t"
    by simp
  from this obtain Tn where "Tn = last t"
    by simp
  then obtain t_nov where "t_nov = map (\<lambda> x. Tn - x) t"
    by blast
  from `sorted t` `Tn = last t`
  have "\<forall> x. x \<in> set t \<longrightarrow>  x \<le> Tn"
    by simp
  from this have "\<forall> x. x \<in> set t_nov \<longrightarrow> x \<ge> 0 \<and> x \<le> Tn"
    by auto
  from this `rastuce t` have "rastuce (reversed t_nov)"
    by simp
  qed
qed

end