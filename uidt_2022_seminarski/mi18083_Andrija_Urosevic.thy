theory mi18083_Andrija_Urosevic
  imports Main

begin

section\<open>Disjunktni Skupovi (Union-Find)\<close>

text\<open>
Struktura podataka disjunktnih skupova predstavlja kolekciju \<open>\<SS> = {S\<^sub>1, S\<^sub>2,..., S\<^sub>k}\<close>
pri čemu su skupovi za \<open>i \<noteq> j\<close> važi \<open>S\<^sub>i \<inter> S\<^sub>j \<noteq> \<emptyset>\<close>. Svaki od skupova identifikujemo sa 
nekim njegovim elementom koga nazivamo predstavnik. Element \<open>x\<close> skupa predstavlja
objekat nad kojim definišemo sledeće operacije:

* \<open>make_set(x)\<close>: Pravi novi disjunktni skup čiji je jedini član objekat x
                 (x je ujedno u predstavnik);

* \<open>union(x, y)\<close>: Spaja dva disjunktna skupa \<open>S\<^sub>x\<close> i \<open>S\<^sub>y\<close> za koje važi \<open>x \<in> S\<^sub>x\<close> i \<open>y \<in> S\<^sub>y\<close>.
                 Dobijamo skup \<open>S\<^sub>x \<union> S\<^sub>y\<close> koji dodajemo u \<open>\<SS>\<close>. Predstavnik dobijenog skupa 
                 je obično jedan od predstavnika skupova \<open>S\<^sub>x\<close> i \<open>S\<^sub>y\<close>. Kako zahtevamo da su 
                 skupovi u kolekcije \<open>\<SS>\<close> disjunktni, onda iz kolekcije izbacujemo 
                 skupove \<open>S\<^sub>x\<close> i \<open>S\<^sub>y\<close>;

* \<open>find_set(x)\<close>: Vraća predstavnika skupa čiji je \<open>x\<close> element.
\<close>

text\<open>Reprezentacija jednog dusjunktnog skupa prirodnih brojeva.\<close>

datatype DisjointSet = MkDisjointSet (parents : "(nat, nat) Map.map") (ranks : "(nat, nat) Map.map")

text\<open>Prazan skup definišemo tako da nema roditelje i rangove\<close>

definition empty_set :: "DisjointSet"
  where
    "empty_set = MkDisjointSet Map.empty Map.empty"

text\<open>Skup sa jednim elementom definišemo tako da je on sam sebi roditelj (tj. on je predstavnik),
     i ranga je 0\<close>

definition make_set :: "nat \<Rightarrow> DisjointSet"
  where
    "make_set x = MkDisjointSet [x \<mapsto> x] [x \<mapsto> 0]"

value "run (parents (make_set 2))"
value "run (ranks (make_set 2))"

lemma make_set_parents:
  shows "parents (make_set x) = [x \<mapsto> x]"
  using make_set_def parents_def
  by auto

lemma make_set_ranks:
  shows "ranks (make_set x) = [x \<mapsto> 0]"
  using make_set_def ranks_def
  by auto

text\<open>Funkcija merge spaja dva medjusobno disjunktna skupa. 
     Ulazni skupovi moraju biti disjunktni.\<close>

definition merge :: "DisjointSet \<Rightarrow> DisjointSet \<Rightarrow> DisjointSet"
  where
    "merge A B = (
        let p1 = parents A;
            p2 = parents B;
            r1 = ranks A;
            r2 = ranks B
        in (MkDisjointSet (p1 ++ p2) (r1 ++ r2))
     )"

value "run (parents (merge (make_set 1) (make_set 2)))"
value "run (ranks (merge (make_set 1) (make_set 2)))"

lemma merge_disjoint_sets_parents:
  fixes A :: DisjointSet
    and B :: DisjointSet
  assumes "dom (parents A) \<noteq> dom (parents B)"
    shows "dom (parents (merge A B)) = dom (parents A ++ parents B)"
  using assms
  using dom_def parents_def merge_def
  by auto

text\<open>Funkcija insert dodaje element u skup. Ako element pripada skupu ne radi ništa.\<close>

definition insert :: "nat \<Rightarrow> DisjointSet \<Rightarrow> DisjointSet"
  where
    "insert x A = (
        let p = (parents A) x;
            S = make_set x
        in (if p = None then merge A S else A)
    )"

lemma insert_parents:
  shows "parents (insert x A) x \<noteq> None"
  using parents_def insert_def merge_def make_set_parents 
  by auto

value "ranks (insert 0 (make_set 3)) 0"

value "run (parents (insert 1 (MkDisjointSet (\<lambda>x. Some 0) [0 \<mapsto> 0])))"
lemma insert_ranks:
  assumes "parents A x = None"
  shows "ranks (insert x A) x \<noteq> None"
  using assms ranks_def insert_def merge_def make_set_ranks
  by auto

value "run (parents (insert 2 (make_set 1)))"
value "run (ranks (insert 2 (make_set 1)))"

value "run (parents (insert 1 (make_set 1)))"
value "run (ranks (insert 1 (make_set 1)))"

function find_set' :: "nat option \<Rightarrow> (nat, nat) Map.map \<Rightarrow> nat option"
  where
    "find_set' None p = None"
  | "find_set' (Some x) p = (
        let y = p x 
         in case y of 
           None \<Rightarrow> None 
         | Some y' \<Rightarrow> (if y' = x then y else find_set' y p)
    )"
  by pat_completeness auto
termination sorry

definition find_set :: "nat \<Rightarrow> DisjointSet \<Rightarrow> nat option"
  where
    "find_set x S = (
        let p = parents S;
            x' = p x
        in (if x' = (Some x) then x' else (find_set' x' p))  
    )"

lemma find_set_insert_empty_set:
  shows "find_set x (insert x empty_set) = Some x"
  using find_set_def insert_def empty_set_def merge_def make_set_parents
  by (smt (verit, ccfv_SIG) DisjointSet.sel(1) fun_upd_same map_add_find_right)

lemma find_set_insert_make_set:
  shows "find_set x (insert x (make_set y)) = Some x"
  using find_set_def insert_def make_set_def merge_def
  by auto

lemma find_set_insert_make_set':
  shows "find_set x (insert y (make_set x)) = Some x"
  using find_set_def insert_def make_set_def merge_def
  by auto

value "find_set 1 (insert 1 (make_set 2))"

function compress :: "nat \<Rightarrow> nat \<Rightarrow> DisjointSet \<Rightarrow> DisjointSet"
  where
    "compress x y S = (
        if x = y then S 
        else (
          let p = (parents S) x 
           in case p of 
                None \<Rightarrow> S 
              | Some p' \<Rightarrow> compress p' y (MkDisjointSet ((parents S) (x \<mapsto> y)) (ranks S))
          )
        )"
  by pat_completeness auto
termination sorry

lemma compress_corectness_empty_set:
  shows "compress x y empty_set = empty_set"
  using empty_set_def
  sorry

value "(parents (compress 3 1 (MkDisjointSet [2 \<mapsto> 1, 3 \<mapsto> 2, 1 \<mapsto> 1] [2 \<mapsto> 0, 3 \<mapsto> 0, 1 \<mapsto> 0])))"

value "([3::nat \<mapsto> 2::nat] (3::nat \<mapsto> 1::nat)) 3"

fun functional_iteration :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "functional_iteration f 0 k j = j"
  | "functional_iteration f (Suc i) k j = f k (functional_iteration f i k j)"

function (sequential) fast_fun :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "fast_fun 0 j = j + 1"
  | "fast_fun (Suc k) j = functional_iteration fast_fun (j + 1) k j"
  by pat_completeness auto
termination sorry

lemma functional_iteration_fast_fun_0:
  assumes "j \<ge> 1"
  shows "functional_iteration fast_fun i 0 j = j + i"
proof (induction i)
  case 0
  then show ?case by auto
next
  case (Suc i)
  have "functional_iteration fast_fun (Suc i) 0 j = fast_fun 0 (functional_iteration fast_fun i 0 j)" 
    by (simp only: functional_iteration.simps(2))
  also have "... = fast_fun 0 (j + i)" using Suc 
    by simp
  also have "... = (j + i) + 1" 
    by (simp only: fast_fun.simps(1))
  finally show ?case by auto
qed

lemma fast_fun_1:
  assumes "j \<ge> 1"
  shows "fast_fun 1 j = 2 * j + 1"
  using assms
  using functional_iteration_fast_fun_0
  by auto

lemma [simp]: 
  fixes i j :: "nat"
  assumes "1 \<le> j" 
  shows "1 \<le> 2 ^ i * (j + 1) - 1"
  using assms
  by (induction i) auto

lemma functional_iteration_fast_fun_1:
  assumes "j \<ge> 1"
  shows "functional_iteration fast_fun i 1 j = 2 ^ i * (j + 1) - 1"
proof (induction i)
  case 0
  then show ?case by auto
next
  case (Suc i)
  have "functional_iteration fast_fun (Suc i) 1 j = fast_fun 1 (functional_iteration fast_fun i 1 j)" 
    by (simp only: functional_iteration.simps(2))
  also have "... = fast_fun 1 (2 ^ i * (j + 1) - 1)" 
    using Suc by simp
  also have "... = 2 * (2 ^ i * (j + 1) - 1) + 1" 
    using fast_fun_1[of "2 ^ i * (j + 1) - 1"]
    using assms
    by fastforce
  also have "... = 2 ^ (i + 1) * (j + 1) - 2 + 1"
    by auto
  also have "... = 2 ^ (i + 1) * (j + 1) - 1"
    by (smt (verit, del_insts) Suc_pred add_2_eq_Suc' add_left_imp_eq assms diff_is_0_eq' le_add_diff_inverse2 nat_0_less_mult_iff nat_1_eq_mult_iff nat_zero_less_power_iff not_less_eq_eq plus_1_eq_Suc zero_less_Suc)
  finally show ?case by auto
qed

lemma fast_fun_2:
  assumes "j \<ge> 1"
  shows "fast_fun 2 j = 2 ^ (j + 1) * (j + 1) - 1"
  using assms
  using fast_fun.simps(2)[of 1 j]
  using functional_iteration_fast_fun_1[of j "(j + 1)"]
  by (metis Suc_1)

lemma fast_fun_0_1:
  shows "fast_fun 0 1 = 2"
  by auto

lemma fast_fun_1_1:
  shows "fast_fun 1 1 = 3"
  by auto

lemma fast_fun_2_1:
  shows "fast_fun 2 1 = 7"
  using fast_fun_2 
  by auto

lemma fast_fun_3_1:
  shows "fast_fun 3 1 = 2047"
proof -
  have "fast_fun 3 1 = functional_iteration fast_fun 2 2 1" 
    by (metis fast_fun.simps(2) numeral_eq_Suc one_add_one pred_numeral_simps(3))
  also have "... = fast_fun 2 (functional_iteration fast_fun 1 2 1)"
    by (metis Suc_1 functional_iteration.simps(2))
  also have "... = fast_fun 2 (fast_fun 2 (functional_iteration fast_fun 0 2 1))"
    by auto
also have "... = fast_fun 2 (fast_fun 2 1)"
    by auto
  also have "... = fast_fun 2 7"
    using fast_fun_2_1 by auto
  also have "... = 2^8 * 8 - 1"
    using fast_fun_2[of 7] by auto
  also have "... = 2 ^ 11 - 1"
    by auto
  also have "... = 2047"
    by auto
  finally show "fast_fun 3 1 = 2047" .
qed

lemma fast_fun_4_1:
  shows "fast_fun 4 1 \<ge> 2^2048"
proof -
  have 1:"fast_fun 2 2047 = 2 ^ 2048 * 2048 - 1"
    by (simp add: fast_fun_2)
  have "fast_fun 4 1 = functional_iteration fast_fun 2 3 1"
    using Suc_1 fast_fun.simps(2) numeral_eq_Suc plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) by presburger
  also have "... = fast_fun 3 (functional_iteration fast_fun 1 3 1)"
    by (metis Suc_1 functional_iteration.simps(2))
  also have "... = fast_fun 3 (fast_fun 3 (functional_iteration fast_fun 0 3 1))"
    by auto
  also have "... = fast_fun 3 (fast_fun 3 1)"
    by auto
  also have "... = fast_fun 3 (2047)"
    using fast_fun_3_1 by auto
  also have "... = functional_iteration fast_fun 2048 2 2047"
    by (metis (no_types, lifting) One_nat_def Suc_1 fast_fun.simps(2) numeral_3_eq_3 numeral_One numeral_plus_numeral semiring_norm(2) semiring_norm(8))
  also have "... = fast_fun 2 (functional_iteration fast_fun 2047 2 2047)"
    using functional_iteration.simps(2) numeral_eq_Suc pred_numeral_simps(2) semiring_norm(26) semiring_norm(27) by presburger
  also have "... \<ge> fast_fun 2 2047"
    sorry
  finally have 2:"fast_fun 4 1 \<ge> fast_fun 2 2047" .
  with 1 2 show ?thesis by auto
qed

definition slow_fun :: "nat \<Rightarrow> nat"
  where
    "slow_fun n = hd (filter (\<lambda> k. fast_fun k 1 \<ge> n) [0::nat, 1, 2, 3, 4, 5])"

lemma [simp]:
  assumes "n \<in> {0::nat..2}"
  shows "slow_fun n = 0"
  using slow_fun_def[of n]
  using fast_fun_0_1
  using assms
  by auto

lemma [simp]:
  assumes "n = 3"
  shows "slow_fun n = 1"
  using slow_fun_def[of n]
  using fast_fun_1_1
  using assms
  by auto

lemma [simp]:
  assumes "n \<in> {4::nat..7}"
  shows "slow_fun n = 2"
  using slow_fun_def[of n]
  using fast_fun_2_1
  using assms
  by auto

lemma [simp]:
  assumes "n \<in> {8::nat..2047}"
  shows "slow_fun n = 3"
  using slow_fun_def[of n]
  using fast_fun_2_1
  using fast_fun_3_1
  using assms
  by auto

lemma [simp]:
  assumes "n \<in> {2047::nat..(2 ^ 2048)}"
  shows "slow_fun n = 4"
  using slow_fun_def[of n]
  using fast_fun_3_1
  using fast_fun_4_1
  using assms
  sorry

lemma [simp]:
  assumes "n \<ge> (2047::nat)"
  shows "slow_fun n = 4"
  sorry

lemma slow_fun_bound [simp]:
  fixes n :: nat
  shows "slow_fun n \<le> 4"
  sorry

end