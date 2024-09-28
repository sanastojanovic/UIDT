theory Novcanice
  imports Main "HOL-Library.Tree" HOL.Orderings
begin

fun gramziva_podela :: "nat \<Rightarrow> nat list" where
  "gramziva_podela x = (if x \<ge> 100 then 100 # gramziva_podela (x - 100)
                else if x \<ge> 50 then 50 # gramziva_podela (x - 50)
                else if x \<ge> 20 then 20 # gramziva_podela (x - 20)
                else if x \<ge> 10 then 10 # gramziva_podela (x - 10)
                else if x \<ge> 5 then  5 # gramziva_podela (x - 5)
                else if x \<ge> 2 then 2 # gramziva_podela (x - 2)
                else if x \<ge> 1 then 1 # gramziva_podela (x - 1)
                else [])"

value "gramziva_podela 283"

primrec suma :: "nat list \<Rightarrow> nat" where 
  "suma [] = 0"
| "suma (x#xs) = x + suma xs"

primrec broj :: "nat list \<Rightarrow> nat" where 
  "broj [] = 0"
| "broj (x#xs) = 1 + broj xs"

value "broj [1, 5, 65]"
value "suma [1, 5, 65]"

primrec novcanice :: "nat list \<Rightarrow> bool" where
  "novcanice [] \<longleftrightarrow> True"
| "novcanice (x#xs) \<longleftrightarrow> (x=100 \<or> x=50 \<or> x=20 \<or> x=10 \<or> x=5 \<or> x=2 \<or> x=1) \<and> novcanice xs"

value "novcanice [1, 6, 10]"
value "novcanice [1, 5, 100]"

definition jeste_podela :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "jeste_podela x l \<longleftrightarrow> (x = suma l) \<and> novcanice l"

value "jeste_podela 34 [10, 10, 10, 2, 2]"
value "jeste_podela 34 [10, 10, 100, 2, 2]"
value "jeste_podela 34 [10, 10, 9, 2, 2, 1]"

definition optimalna_podela :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "optimalna_podela x p \<longleftrightarrow> jeste_podela x p \<and> (\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l)"

primrec broj_y :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where 
  "broj_y y [] = 0"
| "broj_y y (x#xs) = (if x=y then 1 else 0) + broj_y y xs"

value "broj_y 1 [1, 4, 5, 6, 1, 1, 100, 1]"

primrec obrisi :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
   "obrisi y [] = []"
|  "obrisi y (x#xs) = (if x=y then xs else x#(obrisi y xs))"

value "obrisi 4 [1, 4, 5, 6, 1, 1, 100, 4]"


(* Leme za ovu funkciju *)

lemma brisanje[simp]:
  "broj_y y l \<ge> 1 \<longrightarrow> suma l = suma (obrisi y l) + y"
  by (induct l) auto

lemma brisanje2[simp]:
  "broj_y y l \<ge> (Suc n) \<longrightarrow> broj_y y (obrisi y l) \<ge> n"
  by (induct l) auto

lemma brisanje3[simp]:
  "broj_y y l \<ge> 1 \<longrightarrow> broj l = broj (obrisi y l) + 1"
  by (induct l) auto

lemma brisanje4[simp]:
  "novcanice l \<longrightarrow> novcanice (obrisi y l)"
  by (induct l) auto

lemma brisanje5[simp]:
  "y \<noteq> z \<longrightarrow> broj_y y (obrisi z l) = broj_y y l"
  by (induct l) auto

(* Prva grupa lema *)

lemma Najvise_jedna_1_pomocna:
  assumes "jeste_podela x p" "broj_y 1 p \<ge> 2"
  shows "(\<exists>q. jeste_podela x q \<and> broj q < broj p)"
proof- 
  have "suma p = suma (obrisi 1 p) + 1" using \<open>broj_y 1 p \<ge> 2\<close>
    using brisanje[of 1 p] by auto

  have "broj_y 1 (obrisi 1 p) \<ge> 1" using  \<open>broj_y 1 p \<ge> 2\<close>
    using brisanje2[of 1 1 p] by auto

  then have "suma p = suma (obrisi 1 (obrisi 1 p)) + 2"
    using \<open>suma p = suma (obrisi 1 p) + 1\<close> by auto

  then have "suma p = suma (2 # (obrisi 1 (obrisi 1 p)))"
    by (induct p) auto

  obtain q where "q = 2 # (obrisi 1 (obrisi 1 p))" by auto
  then have "broj q < broj p"
    using \<open>broj_y 1 p \<ge> 2\<close> brisanje3[of 1 p] brisanje2[of 1 1 p] by (induct p) auto

  have "suma q = suma p" using \<open>suma p = suma (2 # (obrisi 1 (obrisi 1 p)))\<close> 
    \<open>q = 2 # (obrisi 1 (obrisi 1 p))\<close>  by auto

  then have "jeste_podela x q"
    using \<open>jeste_podela x p\<close> \<open>q = 2 # (obrisi 1 (obrisi 1 p))\<close>
    unfolding jeste_podela_def by auto

  then have "jeste_podela x q \<and> broj q < broj p" using \<open>broj q < broj p\<close> by auto
  then show "(\<exists>q. jeste_podela x q \<and> broj q < broj p)" by (rule_tac x="q" in exI) 
qed

lemma Najvise_jedna_1:
  "optimalna_podela x p \<longrightarrow> broj_y 1 p \<le> 1"
  unfolding optimalna_podela_def
  apply (rule impI)
  apply (erule conjE)
  apply (rule ccontr)
proof-
  assume "jeste_podela x p" "\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l" "\<not> broj_y 1 p \<le> 1"
  obtain q where "jeste_podela x q \<and> broj q < broj p" 
    using \<open>\<not> broj_y 1 p \<le> 1\<close>  Najvise_jedna_1_pomocna[of x p] \<open>jeste_podela x p\<close> by auto

  then show False using \<open>\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l\<close> by auto
qed

lemma Najvise_dve_2_pomocna:
  assumes "jeste_podela x p" "broj_y 2 p \<ge> 3"
  shows "(\<exists>q. jeste_podela x q \<and> broj q < broj p)"
proof- 
  have "suma p = suma (obrisi 2 p) + 2" using \<open>broj_y 2 p \<ge> 3\<close>
    using brisanje[of 2 p] by auto

  obtain p1 where "p1 = (obrisi 2 p)" by auto
  have "broj_y 2 (obrisi 2 p) \<ge> 2" using  \<open>broj_y 2 p \<ge> 3\<close>
    using brisanje2[of 2 2 p] by auto

  then have "suma p = suma (obrisi 2 (obrisi 2 p)) + 4"
    using \<open>suma p = suma (obrisi 2 p) + 2\<close> brisanje[of 2 p1] \<open>p1 = (obrisi 2 p)\<close> by auto

  have "broj_y 2 (obrisi 2 (obrisi 2 p)) \<ge> 1" using  \<open>broj_y 2 (obrisi 2 p) \<ge> 2\<close>
    using brisanje2[of 1 2 p1] \<open>p1 = (obrisi 2 p)\<close> by auto

  obtain p2 where "p2 = (obrisi 2 (obrisi 2 p))" by auto
  then have "suma p = suma (obrisi 2 p2) + 6"
    using \<open>broj_y 2 (obrisi 2 (obrisi 2 p)) \<ge> 1\<close> brisanje[of 2 p2] 
      \<open>suma p = suma (obrisi 2 (obrisi 2 p)) + 4\<close> by auto

  obtain q where "q = 5 # 1 # (obrisi 2 p2)" by auto
  then have "suma q = suma p" using  \<open>suma p = suma (obrisi 2 p2) + 6\<close> by auto
    
  then have "jeste_podela x q"
    using \<open>jeste_podela x p\<close> \<open>q = 5 # 1 # (obrisi 2 p2)\<close> \<open>p2 = (obrisi 2 (obrisi 2 p))\<close>
    unfolding jeste_podela_def by auto

  have "broj p1 = broj p - 1" 
    using \<open>p1 = (obrisi 2 p)\<close>  \<open>broj_y 2 p \<ge> 3\<close> brisanje3[of 2 p] by auto

  then have "broj p2 = broj p - 2" 
    using \<open>p2 = (obrisi 2 (obrisi 2 p))\<close>  \<open>broj_y 2 p \<ge> 3\<close> \<open>p1 = (obrisi 2 p)\<close>
     brisanje3[of 2 p1] by auto

  then have "broj (obrisi 2 p2) = broj p - 3"
    using \<open>broj_y 2 p \<ge> 3\<close> \<open>p2 = (obrisi 2 (obrisi 2 p))\<close> brisanje3[of 2 p2] by auto

  then have "broj q < broj p" 
    using  \<open>q = 5 # 1 # (obrisi 2 p2)\<close> 
    by (metis \<open>1 \<le> broj_y 2 (obrisi 2 (obrisi 2 p))\<close> \<open>2 \<le> broj_y 2 (obrisi 2 p)\<close> \<open>broj p1 = broj p - 1\<close> \<open>p1 = obrisi 2 p\<close> \<open>p2 = obrisi 2 (obrisi 2 p)\<close> add.commute add_leD2 brisanje3 broj.simps(2) less_add_one less_diff_conv nat_1_add_1)

  then have "jeste_podela x q \<and> broj q < broj p" using \<open>jeste_podela x q\<close> by auto
  then show "(\<exists>q. jeste_podela x q \<and> broj q < broj p)" by (rule_tac x="q" in exI) 
qed

lemma Najvise_dve_2:
  "optimalna_podela x p \<longrightarrow> broj_y 2 p \<le> 2"
   unfolding optimalna_podela_def
  apply (rule impI)
  apply (erule conjE)
  apply (rule ccontr)
proof-
  assume "jeste_podela x p" "\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l" "\<not> broj_y 2 p \<le> 2"
  obtain q where "jeste_podela x q \<and> broj q < broj p" 
    using \<open>\<not> broj_y 2 p \<le> 2\<close>  Najvise_dve_2_pomocna[of x p] \<open>jeste_podela x p\<close> by auto

  then show False using \<open>\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l\<close> by auto
qed

lemma Najvise_jedna_5_pomocna:
  assumes "jeste_podela x p" "broj_y 5 p \<ge> 2"
  shows "(\<exists>q. jeste_podela x q \<and> broj q < broj p)"
proof- 
  have "suma p = suma (obrisi 5 p) + 5" using \<open>broj_y 5 p \<ge> 2\<close>
    using brisanje[of 5 p] by auto

  have "broj_y 5 (obrisi 5 p) \<ge> 1" using  \<open>broj_y 5 p \<ge> 2\<close>  by auto

  then have "suma p = suma (obrisi 5 (obrisi 5 p)) + 10"
    using \<open>suma p = suma (obrisi 5 p) + 5\<close> by auto

  then have "suma p = suma (10 # (obrisi 5 (obrisi 5 p)))"
    by (induct p) auto

  obtain q where "q = 10 # (obrisi 5 (obrisi 5 p))" by auto
  then have "broj q < broj p"
    using \<open>broj_y 5 p \<ge> 2\<close> brisanje3[of 5 p] brisanje2[of 1 5 p] by (induct p) auto

  have "suma q = suma p" using \<open>suma p = suma (10 # (obrisi 5 (obrisi 5 p)))\<close> 
    \<open>q = 10 # (obrisi 5 (obrisi 5 p))\<close>  by auto

  then have "jeste_podela x q"
    using \<open>jeste_podela x p\<close> \<open>q = 10 # (obrisi 5 (obrisi 5 p))\<close>
    unfolding jeste_podela_def by auto

  then have "jeste_podela x q \<and> broj q < broj p" using \<open>broj q < broj p\<close> by auto
  then show "(\<exists>q. jeste_podela x q \<and> broj q < broj p)" by (rule_tac x="q" in exI) 
qed

lemma Najvise_jedna_5:
  "optimalna_podela x p \<longrightarrow> broj_y 5 p \<le> 1"
  unfolding optimalna_podela_def
  apply (rule impI)
  apply (erule conjE)
  apply (rule ccontr)
proof-
  assume "jeste_podela x p" "\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l" "\<not> broj_y 5 p \<le> 1"
  obtain q where "jeste_podela x q \<and> broj q < broj p" 
    using \<open>\<not> broj_y 5 p \<le> 1\<close>  Najvise_jedna_5_pomocna[of x p] \<open>jeste_podela x p\<close> by auto

  then show False using \<open>\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l\<close> by auto
qed

lemma Nije_moguce_221_pomocna:
  assumes "jeste_podela x p" "broj_y 1 p \<ge> 1" "broj_y 2 p \<ge> 2"
  shows "(\<exists>q. jeste_podela x q \<and> broj q < broj p)"
proof- 
  have "suma p = suma (obrisi 2 p) + 2" using \<open>broj_y 2 p \<ge> 2\<close>
    using brisanje[of 2 p] by auto

  obtain p1 where "p1 = (obrisi 2 p)" by auto
  have "broj_y 2 (obrisi 2 p) \<ge> 1" using  \<open>broj_y 2 p \<ge> 2\<close>
    using brisanje2[of 1 2 p] by auto

  then have "suma p = suma (obrisi 2 (obrisi 2 p)) + 4"
    using \<open>suma p = suma (obrisi 2 p) + 2\<close> brisanje[of 2 p1] \<open>p1 = (obrisi 2 p)\<close> by auto

  obtain p2 where "p2 = (obrisi 2 (obrisi 2 p))" by auto
  then have "suma p = suma (obrisi 1 p2) + 5"
    using \<open>broj_y 1 p \<ge> 1\<close> brisanje[of 1 p2] 
      \<open>suma p = suma (obrisi 2 (obrisi 2 p)) + 4\<close> by auto 

  obtain q where "q = 5 # (obrisi 1 p2)" by auto
  then have "suma q = suma p" using  \<open>suma p = suma (obrisi 1 p2) + 5\<close> by auto
    
  then have "jeste_podela x q"
    using \<open>jeste_podela x p\<close> \<open>q = 5 # (obrisi 1 p2)\<close> \<open>p2 = (obrisi 2 (obrisi 2 p))\<close>
    unfolding jeste_podela_def by auto

  have "broj p1 = broj p - 1" 
    using \<open>p1 = (obrisi 2 p)\<close>  \<open>broj_y 2 p \<ge> 2\<close> brisanje3[of 2 p] by auto

  then have "broj p2 = broj p - 2" 
    using \<open>p2 = (obrisi 2 (obrisi 2 p))\<close>  \<open>broj_y 2 p \<ge> 2\<close> \<open>p1 = (obrisi 2 p)\<close>
     brisanje3[of 2 p1] by auto

  then have "broj (obrisi 1 p2) = broj p - 3"
    using \<open>broj_y 1 p \<ge> 1\<close> \<open>p2 = (obrisi 2 (obrisi 2 p))\<close> brisanje3[of 1 p2] by auto

  then have "broj q < broj p" 
    using  \<open>q = 5 # (obrisi 1 p2)\<close> 
    using \<open>1 \<le> broj_y 2 (obrisi 2 p)\<close> \<open>broj p1 = broj p - 1\<close> \<open>p1 = obrisi 2 p\<close> 
    by (induct p) auto

  then have "jeste_podela x q \<and> broj q < broj p" using \<open>jeste_podela x q\<close> by auto
  then show "(\<exists>q. jeste_podela x q \<and> broj q < broj p)" by (rule_tac x="q" in exI) 
qed

lemma Nije_moguce_221:
  "optimalna_podela x p \<longrightarrow> \<not>(broj_y 1 p \<ge> 1 \<and> broj_y 2 p \<ge> 2)"
unfolding optimalna_podela_def
  apply (rule impI)
  apply (erule conjE)
  apply (rule ccontr)
proof-
  assume "jeste_podela x p" "\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l" 
        "\<not>\<not>(broj_y 1 p \<ge> 1 \<and> broj_y 2 p \<ge> 2)"
  then have "(broj_y 1 p \<ge> 1 \<and> broj_y 2 p \<ge> 2)" by auto
  then obtain q where "jeste_podela x q \<and> broj q < broj p" 
    using  Nije_moguce_221_pomocna[of x p] \<open>jeste_podela x p\<close> by auto

  then show False using \<open>\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l\<close> by auto
qed

lemma Najvise_jedna_10_pomocna:
  assumes "jeste_podela x p" "broj_y 10 p \<ge> 2"
  shows "(\<exists>q. jeste_podela x q \<and> broj q < broj p)"
proof- 
  have "suma p = suma (obrisi 10 p) + 10" using \<open>broj_y 10 p \<ge> 2\<close>
    using brisanje[of 1 p] by auto

  have "broj_y 10 (obrisi 10 p) \<ge> 1" using  \<open>broj_y 10 p \<ge> 2\<close>
    using brisanje2[of 1 10 p] by auto

  then have "suma p = suma (obrisi 10 (obrisi 10 p)) + 20"
    using \<open>suma p = suma (obrisi 10 p) + 10\<close> by auto

  then have "suma p = suma (20 # (obrisi 10 (obrisi 10 p)))"
    by (induct p) auto

  obtain q where "q = 20 # (obrisi 10 (obrisi 10 p))" by auto
  then have "broj q < broj p"
    using \<open>broj_y 10 p \<ge> 2\<close> brisanje3[of 10 p] brisanje2[of 1 10 p] by (induct p) auto

  have "suma q = suma p" using \<open>suma p = suma (20 # (obrisi 10 (obrisi 10 p)))\<close> 
    \<open>q = 20 # (obrisi 10 (obrisi 10 p))\<close>  by auto

  then have "jeste_podela x q"
    using \<open>jeste_podela x p\<close> \<open>q = 20 # (obrisi 10 (obrisi 10 p))\<close>
    unfolding jeste_podela_def by auto

  then have "jeste_podela x q \<and> broj q < broj p" using \<open>broj q < broj p\<close> by auto
  then show "(\<exists>q. jeste_podela x q \<and> broj q < broj p)" by (rule_tac x="q" in exI) 
qed

lemma Najvise_jedna_10:
  "optimalna_podela x p \<longrightarrow> broj_y 10 p \<le> 1"
  unfolding optimalna_podela_def
  apply (rule impI)
  apply (erule conjE)
  apply (rule ccontr)
proof-
  assume "jeste_podela x p" "\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l" "\<not> broj_y 10 p \<le> 1"
  obtain q where "jeste_podela x q \<and> broj q < broj p" 
    using \<open>\<not> broj_y 10 p \<le> 1\<close>  Najvise_jedna_10_pomocna[of x p] \<open>jeste_podela x p\<close> by auto

  then show False using \<open>\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l\<close> by auto
qed

lemma Najvise_dve_20_pomocna:
  assumes "jeste_podela x p" "broj_y 20 p \<ge> 3"
  shows "(\<exists>q. jeste_podela x q \<and> broj q < broj p)"
proof- 
  have "suma p = suma (obrisi 20 p) + 20" using \<open>broj_y 20 p \<ge> 3\<close>
    using brisanje[of 20 p] by auto

  obtain p1 where "p1 = (obrisi 20 p)" by auto
  have "broj_y 20 (obrisi 20 p) \<ge> 2" using  \<open>broj_y 20 p \<ge> 3\<close>
    using brisanje2[of 2 20 p] by auto

  then have "suma p = suma (obrisi 20 (obrisi 20 p)) + 40"
    using \<open>suma p = suma (obrisi 20 p) + 20\<close> brisanje[of 20 p1] \<open>p1 = (obrisi 20 p)\<close> 
    by (metis add.assoc add_leE nat_1_add_1 numeral_Bit0)

  have "broj_y 20 (obrisi 20 (obrisi 20 p)) \<ge> 1" using  \<open>broj_y 20 (obrisi 20 p) \<ge> 2\<close>
    using brisanje2[of 1 20 p1] \<open>p1 = (obrisi 20 p)\<close> by auto

  obtain p2 where "p2 = (obrisi 20 (obrisi 20 p))" by auto
  then have "suma p = suma (obrisi 20 p2) + 60"
    using \<open>broj_y 20 (obrisi 20 (obrisi 20 p)) \<ge> 1\<close> brisanje[of 20 p2] 
      \<open>suma p = suma (obrisi 20 (obrisi 20 p)) + 40\<close> by auto

  obtain q where "q = 50 # 10 # (obrisi 20 p2)" by auto
  then have "suma q = suma p" using  \<open>suma p = suma (obrisi 20 p2) + 60\<close> by auto
    
  then have "jeste_podela x q"
    using \<open>jeste_podela x p\<close> \<open>q = 50 # 10 # (obrisi 20 p2)\<close> \<open>p2 = (obrisi 20 (obrisi 20 p))\<close>
    unfolding jeste_podela_def by auto

  have "broj p1 = broj p - 1" 
    using \<open>p1 = (obrisi 20 p)\<close>  \<open>broj_y 20 p \<ge> 3\<close> brisanje3[of 20 p] by auto

  then have "broj p2 = broj p - 2" 
    using \<open>p2 = (obrisi 20 (obrisi 20 p))\<close>  \<open>broj_y 20 p \<ge> 3\<close> \<open>p1 = (obrisi 20 p)\<close>
     brisanje3[of 20 p1] by auto

  then have "broj (obrisi 20 p2) = broj p - 3"
    using \<open>broj_y 20 p \<ge> 3\<close> \<open>p2 = (obrisi 20 (obrisi 20 p))\<close> brisanje3[of 20 p2] by auto

  then have "broj q < broj p" 
    using  \<open>q = 50 # 10 # (obrisi 20 p2)\<close> 
    by (metis \<open>1 \<le> broj_y 20 (obrisi 20 (obrisi 20 p))\<close> \<open>2 \<le> broj_y 20 (obrisi 20 p)\<close> \<open>broj p1 = broj p - 1\<close> \<open>p1 = obrisi 20 p\<close> \<open>p2 = obrisi 20 (obrisi 20 p)\<close> add.commute add_leD2 brisanje3 broj.simps(2) less_add_one less_diff_conv nat_1_add_1)

  then have "jeste_podela x q \<and> broj q < broj p" using \<open>jeste_podela x q\<close> by auto
  then show "(\<exists>q. jeste_podela x q \<and> broj q < broj p)" by (rule_tac x="q" in exI) 
qed

lemma Najvise_dve_20:
  "optimalna_podela x p \<longrightarrow> broj_y 20 p \<le> 2"
   unfolding optimalna_podela_def
  apply (rule impI)
  apply (erule conjE)
  apply (rule ccontr)
proof-
  assume "jeste_podela x p" "\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l" "\<not> broj_y 20 p \<le> 2"
  obtain q where "jeste_podela x q \<and> broj q < broj p" 
    using \<open>\<not> broj_y 20 p \<le> 2\<close>  Najvise_dve_20_pomocna[of x p] \<open>jeste_podela x p\<close> by auto

  then show False using \<open>\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l\<close> by auto
qed

lemma Najvise_jedna_50_pomocna:
  assumes "jeste_podela x p" "broj_y 50 p \<ge> 2"
  shows "(\<exists>q. jeste_podela x q \<and> broj q < broj p)"
proof- 
  have "suma p = suma (obrisi 50 p) + 50" using \<open>broj_y 50 p \<ge> 2\<close>
    using brisanje[of 50 p] by auto

  have "broj_y 50 (obrisi 50 p) \<ge> 1" using  \<open>broj_y 50 p \<ge> 2\<close>  by auto

  then have "suma p = suma (obrisi 50 (obrisi 50 p)) + 100"
    using \<open>suma p = suma (obrisi 50 p) + 50\<close> by auto

  then have "suma p = suma (100 # (obrisi 50 (obrisi 50 p)))"
    by (induct p) auto

  obtain q where "q = 100 # (obrisi 50 (obrisi 50 p))" by auto
  then have "broj q < broj p"
    using \<open>broj_y 50 p \<ge> 2\<close> brisanje3[of 50 p] brisanje2[of 1 50 p] by (induct p) auto

  have "suma q = suma p" using \<open>suma p = suma (100 # (obrisi 50 (obrisi 50 p)))\<close> 
    \<open>q = 100 # (obrisi 50 (obrisi 50 p))\<close>  by auto

  then have "jeste_podela x q"
    using \<open>jeste_podela x p\<close> \<open>q = 100 # (obrisi 50 (obrisi 50 p))\<close>
    unfolding jeste_podela_def by auto

  then have "jeste_podela x q \<and> broj q < broj p" using \<open>broj q < broj p\<close> by auto
  then show "(\<exists>q. jeste_podela x q \<and> broj q < broj p)" by (rule_tac x="q" in exI) 
qed

lemma Najvise_jedna_50:
  "optimalna_podela x p \<longrightarrow> broj_y 50 p \<le> 1"
  unfolding optimalna_podela_def
  apply (rule impI)
  apply (erule conjE)
  apply (rule ccontr)
proof-
  assume "jeste_podela x p" "\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l" "\<not> broj_y 50 p \<le> 1"
  obtain q where "jeste_podela x q \<and> broj q < broj p" 
    using \<open>\<not> broj_y 50 p \<le> 1\<close>  Najvise_jedna_50_pomocna[of x p] \<open>jeste_podela x p\<close> by auto

  then show False using \<open>\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l\<close> by auto
qed

lemma Nije_moguce_202010_pomocna:
  assumes "jeste_podela x p" "broj_y 10 p \<ge> 1" "broj_y 20 p \<ge> 2"
  shows "(\<exists>q. jeste_podela x q \<and> broj q < broj p)"
proof- 
  have "suma p = suma (obrisi 20 p) + 20" using \<open>broj_y 20 p \<ge> 2\<close>
    using brisanje[of 20 p] by auto

  obtain p1 where "p1 = (obrisi 20 p)" by auto
  have "broj_y 20 (obrisi 20 p) \<ge> 1" using  \<open>broj_y 20 p \<ge> 2\<close>
    using brisanje2[of 1 20 p] by auto

  then have "suma p = suma (obrisi 20 (obrisi 20 p)) + 40"
    using \<open>suma p = suma (obrisi 20 p) + 20\<close> brisanje[of 20 p1] \<open>p1 = (obrisi 20 p)\<close> by auto

  obtain p2 where "p2 = (obrisi 20 (obrisi 20 p))" by auto
  then have "suma p = suma (obrisi 10 p2) + 50"
    using \<open>broj_y 10 p \<ge> 1\<close> brisanje[of 10 p2] 
      \<open>suma p = suma (obrisi 20 (obrisi 20 p)) + 40\<close> 
    by (simp add: ab_semigroup_add_class.add_ac(1) numeral_Bit0 numeral_Bit1 semiring_norm(87) semiring_norm(89))

  obtain q where "q = 50 # (obrisi 10 p2)" by auto
  then have "suma q = suma p" using  \<open>suma p = suma (obrisi 10 p2) + 50\<close> by auto
    
  then have "jeste_podela x q"
    using \<open>jeste_podela x p\<close> \<open>q = 50 # (obrisi 10 p2)\<close> \<open>p2 = (obrisi 20 (obrisi 20 p))\<close>
    unfolding jeste_podela_def by auto

  have "broj p1 = broj p - 1" 
    using \<open>p1 = (obrisi 20 p)\<close>  \<open>broj_y 20 p \<ge> 2\<close> brisanje3[of 20 p] by auto

  then have "broj p2 = broj p - 2" 
    using \<open>p2 = (obrisi 20 (obrisi 20 p))\<close>  \<open>broj_y 20 p \<ge> 2\<close> \<open>p1 = (obrisi 20 p)\<close>
     brisanje3[of 20 p1] by auto

  then have "broj (obrisi 10 p2) = broj p - 3"
    using \<open>broj_y 10 p \<ge> 1\<close> \<open>p2 = (obrisi 20 (obrisi 20 p))\<close> brisanje3[of 10 p2] by auto

  then have "broj q < broj p" 
    using  \<open>q = 50 # (obrisi 10 p2)\<close> 
    using \<open>1 \<le> broj_y 20 (obrisi 20 p)\<close> \<open>broj p1 = broj p - 1\<close> \<open>p1 = obrisi 20 p\<close> 
    by (induct p) auto

  then have "jeste_podela x q \<and> broj q < broj p" using \<open>jeste_podela x q\<close> by auto
  then show "(\<exists>q. jeste_podela x q \<and> broj q < broj p)" by (rule_tac x="q" in exI) 
qed

lemma Nije_moguce_202010:
  "optimalna_podela x p \<longrightarrow> \<not>(broj_y 10 p \<ge> 1 \<and> broj_y 20 p \<ge> 2)"
unfolding optimalna_podela_def
  apply (rule impI)
  apply (erule conjE)
  apply (rule ccontr)
proof-
  assume "jeste_podela x p" "\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l" 
        "\<not>\<not>(broj_y 10 p \<ge> 1 \<and> broj_y 20 p \<ge> 2)"
  then have "(broj_y 10 p \<ge> 1 \<and> broj_y 20 p \<ge> 2)" by auto
  then obtain q where "jeste_podela x q \<and> broj q < broj p" 
    using  Nije_moguce_202010_pomocna[of x p] \<open>jeste_podela x p\<close> by auto

  then show False using \<open>\<forall>l. jeste_podela x l \<longrightarrow> broj p \<le> broj l\<close> by auto
qed

(* Druga grupa lema *)

lemma nepostojanje:
  "n \<notin> set p \<longleftrightarrow> broj_y n p = 0"
  by (induct p) auto

lemma nepostojanje2:
  "n \<in> set p \<longleftrightarrow> broj_y n p \<ge> 1"
  by (induct p) auto

lemma ukupno:
  "novcanice p \<longrightarrow> broj p = broj_y 1 p + broj_y 2 p + broj_y 5 p +
  broj_y 10 p + broj_y 20 p + broj_y 50 p + broj_y 100 p"
  unfolding novcanice_def
  by (induct p) auto

lemma ukupno2:
  "novcanice p \<longrightarrow> suma p = broj_y 1 p + 2 * broj_y 2 p + 5 * broj_y 5 p +
  10 * broj_y 10 p + 20 * broj_y 20 p + 50 * broj_y 50 p + 100 * broj_y 100 p"
  unfolding novcanice_def
  by (induct p) auto

lemma brisanje6[simp]:
  "broj_y y l = (Suc n) \<longrightarrow> broj_y y (obrisi y l) = n"
  by (induct l) auto

lemma OstajeOptimalna:
  "optimalna_podela x p \<and> n \<in> set p \<longrightarrow> optimalna_podela (x-n) (obrisi n p)"
  unfolding optimalna_podela_def jeste_podela_def
  apply (rule impI)
  apply (erule conjE)+
  apply (rule conjI)+
    apply auto
   apply (metis brisanje[of n p] nepostojanje[of n p]
        add_diff_cancel_right' less_one verit_comp_simplify1(3))
proof-
  fix l
  assume "n \<in> set p" "\<forall>l. suma p = suma l \<and> novcanice l \<longrightarrow> broj p \<le> broj l"
     "x = suma p" "novcanice p" "suma p - n = suma l" "novcanice l"
  
  then show "broj (obrisi n p) \<le> broj l"
  proof (cases "broj (obrisi n p) \<le> broj l")
    case True
    then show ?thesis by auto
  next
    case False
    then have "broj (obrisi n p) + 1 > broj l + 1" by auto
    have "broj p = broj (obrisi n p) + 1" 
      using brisanje3[of n p] nepostojanje2[of n p] \<open>n \<in> set p\<close> by auto
    then have "broj p > broj l + 1" using \<open>broj (obrisi n p) + 1 > broj l + 1\<close> by auto
 
    obtain k where "k = n#l" by auto
    then have "suma p = suma k" using \<open>suma p - n = suma l\<close> suma.simps(2)[of n l]
      by (metis \<open>n \<in> set p\<close> brisanje le_add2 nepostojanje2 
            ordered_cancel_comm_monoid_diff_class.add_diff_inverse)

    have "n \<in> {1, 2, 5, 10, 20, 50, 100}" using \<open>n \<in> set p\<close> \<open>novcanice p\<close> 
      by (induct p) auto
    then have "novcanice k" using \<open>novcanice l\<close> \<open>k = n#l\<close> 
      unfolding novcanice_def by auto

    have "broj k = broj l + 1" using \<open>k = n#l\<close> by auto
    then have "~(broj p \<le> broj k)" using \<open>broj p > broj l + 1\<close> by auto
    then have False using \<open>\<forall>l. suma p = suma l \<and> novcanice l \<longrightarrow> broj p \<le> broj l\<close>
        \<open>novcanice k\<close> \<open>suma p = suma k\<close> by (erule_tac x="k" in allE) auto

    then show ?thesis by auto
  qed
qed

lemma ZbirOptimalnih:
  "optimalna_podela x p \<and> optimalna_podela y q \<and>
    (set p \<inter> set q = {}) \<longrightarrow> optimalna_podela (x + y) (p @ q)"
  unfolding optimalna_podela_def jeste_podela_def
  oops

lemma Sa_1_najvise_1:
  "optimalna_podela x p \<and> {2, 5, 10, 20, 50, 100} \<inter> set p = {} \<longrightarrow> x \<le> 1"
  apply (rule impI)
  apply (erule conjE)
proof-
  assume "optimalna_podela x p" "{2, 5, 10, 20, 50, 100} \<inter> set p = {}"
  then have "broj_y 1 p \<le> 1" using Najvise_jedna_1 by auto

  have "2 \<notin> set p" using \<open>{2, 5, 10, 20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 2 p = 0" using nepostojanje by auto
  have "5 \<notin> set p" using \<open>{2, 5, 10, 20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 5 p = 0" using nepostojanje by auto
  have "10 \<notin> set p" using \<open>{2, 5, 10, 20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 10 p = 0" using nepostojanje by auto
  have "20 \<notin> set p" using \<open>{2, 5, 10, 20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 20 p = 0" using nepostojanje by auto
  have "50 \<notin> set p" using \<open>{2, 5, 10, 20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 50 p = 0" using nepostojanje by auto
  have "100 \<notin> set p" using \<open>{2, 5, 10, 20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 100 p = 0" using nepostojanje by auto

  have "novcanice p" "suma p = x" using \<open>optimalna_podela x p\<close> 
    unfolding optimalna_podela_def jeste_podela_def by auto
  then have "suma p \<le> 1" using \<open>broj_y 1 p \<le> 1\<close> \<open>broj_y 2 p = 0\<close> \<open>broj_y 5 p = 0\<close>
    \<open>broj_y 10 p = 0\<close> \<open>broj_y 20 p = 0\<close> \<open>broj_y 50 p = 0\<close> \<open>broj_y 100 p = 0\<close>
     ukupno2 by auto

  then show "x \<le> 1" using \<open>suma p = x\<close> by auto
qed

lemma Sa_12_najvise_4:
  "optimalna_podela x p \<and> {5, 10, 20, 50, 100} \<inter> set p = {} \<longrightarrow> x \<le> 4"
  apply (rule impI)
  apply (erule conjE)
proof-
  assume "optimalna_podela x p" "{5, 10, 20, 50, 100} \<inter> set p = {}"
  then have "broj_y 1 p \<le> 1" using Najvise_jedna_1 by auto
  have "broj_y 2 p \<le> 2" using \<open>optimalna_podela x p\<close> Najvise_dve_2 by auto
  have "\<not>(broj_y 1 p \<ge> 1 \<and> broj_y 2 p \<ge> 2)" using \<open>optimalna_podela x p\<close> 
        Nije_moguce_221 by auto
  then have "broj_y 1 p = 0 \<or> broj_y 2 p \<le> 1" by auto

  have "5 \<notin> set p" using \<open>{5, 10, 20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 5 p = 0" using nepostojanje by auto
  have "10 \<notin> set p" using \<open>{5, 10, 20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 10 p = 0" using nepostojanje by auto
  have "20 \<notin> set p" using \<open>{5, 10, 20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 20 p = 0" using nepostojanje by auto
  have "50 \<notin> set p" using \<open>{5, 10, 20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 50 p = 0" using nepostojanje by auto
  have "100 \<notin> set p" using \<open>{5, 10, 20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 100 p = 0" using nepostojanje by auto

  have "novcanice p" "suma p = x" using \<open>optimalna_podela x p\<close> 
    unfolding optimalna_podela_def jeste_podela_def by auto


  then show "x \<le> 4"
  proof (cases "broj_y 1 p = 0")
    case True
    then have "suma p \<le> 4" using \<open>broj_y 1 p = 0\<close> \<open>broj_y 2 p \<le> 2\<close> \<open>broj_y 5 p = 0\<close>
    \<open>broj_y 10 p = 0\<close> \<open>broj_y 20 p = 0\<close> \<open>broj_y 50 p = 0\<close> \<open>broj_y 100 p = 0\<close>
     ukupno2 \<open>novcanice p\<close> by auto
    then show ?thesis using \<open>suma p = x\<close> by auto
  next
    case False
    then have "broj_y 2 p \<le> 1" using \<open>broj_y 1 p = 0 \<or> broj_y 2 p \<le> 1\<close> by auto
    then have "suma p \<le> 3" using \<open>broj_y 1 p \<le> 1\<close> \<open>broj_y 2 p \<le> 1\<close> \<open>broj_y 5 p = 0\<close>
    \<open>broj_y 10 p = 0\<close> \<open>broj_y 20 p = 0\<close> \<open>broj_y 50 p = 0\<close> \<open>broj_y 100 p = 0\<close>
     ukupno2 \<open>novcanice p\<close> by auto
    then show ?thesis using \<open>suma p = x\<close> by auto
  qed
qed

lemma Sa_125_najvise_9:
  "optimalna_podela x p \<and> {10, 20, 50, 100} \<inter> set p = {} \<longrightarrow> x \<le> 9"
  apply (rule impI)
  apply (erule conjE)
proof-
  assume "optimalna_podela x p" "{10, 20, 50, 100} \<inter> set p = {}"
  then have "broj_y 1 p \<le> 1" using Najvise_jedna_1 by auto
  have "broj_y 2 p \<le> 2" using \<open>optimalna_podela x p\<close> Najvise_dve_2 by auto
  have "\<not>(broj_y 1 p \<ge> 1 \<and> broj_y 2 p \<ge> 2)" using \<open>optimalna_podela x p\<close> 
        Nije_moguce_221 by auto
  then have "broj_y 1 p = 0 \<or> broj_y 2 p \<le> 1" by auto
  have "broj_y 5 p \<le> 1" using \<open>optimalna_podela x p\<close>  Najvise_jedna_5 by auto

  have "10 \<notin> set p" using \<open>{10, 20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 10 p = 0" using nepostojanje by auto
  have "20 \<notin> set p" using \<open>{10, 20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 20 p = 0" using nepostojanje by auto
  have "50 \<notin> set p" using \<open>{10, 20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 50 p = 0" using nepostojanje by auto
  have "100 \<notin> set p" using \<open>{10, 20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 100 p = 0" using nepostojanje by auto

  have "novcanice p" "suma p = x" using \<open>optimalna_podela x p\<close> 
    unfolding optimalna_podela_def jeste_podela_def by auto


  then show "x \<le> 9"
  proof (cases "broj_y 1 p = 0")
    case True
    then have "suma p \<le> 9" using \<open>broj_y 1 p = 0\<close> \<open>broj_y 2 p \<le> 2\<close> \<open>broj_y 5 p \<le> 1\<close>
    \<open>broj_y 10 p = 0\<close> \<open>broj_y 20 p = 0\<close> \<open>broj_y 50 p = 0\<close> \<open>broj_y 100 p = 0\<close>
     ukupno2 \<open>novcanice p\<close> by auto
    then show ?thesis using \<open>suma p = x\<close> by auto
  next
    case False
    then have "broj_y 2 p \<le> 1" using \<open>broj_y 1 p = 0 \<or> broj_y 2 p \<le> 1\<close> by auto
    then have "suma p \<le> 9" using \<open>broj_y 1 p \<le> 1\<close> \<open>broj_y 2 p \<le> 1\<close> \<open>broj_y 5 p \<le> 1\<close>
    \<open>broj_y 10 p = 0\<close> \<open>broj_y 20 p = 0\<close> \<open>broj_y 50 p = 0\<close> \<open>broj_y 100 p = 0\<close>
     ukupno2 \<open>novcanice p\<close> by auto
    then show ?thesis using \<open>suma p = x\<close> by auto
  qed
qed

lemma Sa_12510_najvise_19:
  "optimalna_podela x p \<and> {20, 50, 100} \<inter> set p = {} \<longrightarrow> x \<le> 19"
  apply (rule impI)
  apply (erule conjE)
proof-
  assume "optimalna_podela x p" "{20, 50, 100} \<inter> set p = {}"
  then have "broj_y 1 p \<le> 1" using Najvise_jedna_1 by auto
  have "broj_y 2 p \<le> 2" using \<open>optimalna_podela x p\<close> Najvise_dve_2 by auto
  have "\<not>(broj_y 1 p \<ge> 1 \<and> broj_y 2 p \<ge> 2)" using \<open>optimalna_podela x p\<close> 
        Nije_moguce_221 by auto
  then have "broj_y 1 p = 0 \<or> broj_y 2 p \<le> 1" by auto
  have "broj_y 5 p \<le> 1" using \<open>optimalna_podela x p\<close>  Najvise_jedna_5 by auto
  have "broj_y 10 p \<le> 1" using \<open>optimalna_podela x p\<close> Najvise_jedna_10 by auto

  have "20 \<notin> set p" using \<open>{20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 20 p = 0" using nepostojanje by auto
  have "50 \<notin> set p" using \<open>{20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 50 p = 0" using nepostojanje by auto
  have "100 \<notin> set p" using \<open>{20, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 100 p = 0" using nepostojanje by auto

  have "novcanice p" "suma p = x" using \<open>optimalna_podela x p\<close> 
    unfolding optimalna_podela_def jeste_podela_def by auto


  then show "x \<le> 19"
  proof(cases "broj_y 10 p = 0")
    case True
    then have "10 \<notin> set p" using nepostojanje by auto
    then have "{10, 20, 50, 100} \<inter> set p = {}" using \<open>{20, 50, 100} \<inter> set p = {}\<close> by auto
    then show ?thesis using Sa_125_najvise_9[of x p] \<open>optimalna_podela x p\<close> by auto 
  next
    case False
    then have "broj_y 10 p = 1" using \<open>broj_y 10 p \<le> 1\<close> by auto
    obtain q where "q = obrisi 10 p" by auto
    then have "broj_y 10 q = 0" using \<open>broj_y 10 p = 1\<close> brisanje6[of 10 p 0] by auto
    then have "broj_y 20 q = 0" "broj_y 50 q = 0"  "broj_y 100 q = 0"
      using \<open>broj_y 20 p = 0\<close>  \<open>broj_y 50 p = 0\<close>  \<open>broj_y 100 p = 0\<close> \<open>q = obrisi 10 p\<close> by auto
    then have "10 \<notin> set q" "20 \<notin> set q" "50 \<notin> set q" "100 \<notin> set q" 
      using \<open>broj_y 10 q = 0\<close> using nepostojanje by auto 
    then have "{10, 20, 50, 100} \<inter> set q = {}" by auto 
    have "10 \<in> set p" using nepostojanje[of 10 p] \<open>broj_y 10 p = 1\<close> by auto
    obtain y where "y = x - 10" by auto
    then have "optimalna_podela y q" using OstajeOptimalna[of x p 10] \<open>10 \<in> set p\<close> 
      \<open>q = obrisi 10 p\<close> \<open>optimalna_podela x p\<close> by auto
    then show ?thesis using  Sa_125_najvise_9[of y q]  \<open>y = x - 10\<close>
         \<open>{10, 20, 50, 100} \<inter> set q = {}\<close> \<open>optimalna_podela y q\<close> by auto
  qed
qed

lemma Sa_1020_najvise_40:
  "optimalna_podela x p \<and> {1, 2, 5, 50, 100} \<inter> set p = {} \<longrightarrow> x \<le> 40"
  apply (rule impI)
  apply (erule conjE)
proof-
  assume "optimalna_podela x p" "{1, 2, 5, 50, 100} \<inter> set p = {}"
  then have "broj_y 10 p \<le> 1" using Najvise_jedna_10 by auto
  have "broj_y 20 p \<le> 2" using \<open>optimalna_podela x p\<close> Najvise_dve_20 by auto
  have "\<not>(broj_y 10 p \<ge> 1 \<and> broj_y 20 p \<ge> 2)" using \<open>optimalna_podela x p\<close> 
        Nije_moguce_202010 by auto
  then have "broj_y 10 p = 0 \<or> broj_y 20 p \<le> 1" by auto

  have "5 \<notin> set p" using \<open>{1, 2, 5, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 5 p = 0" using nepostojanje by auto
  have "1 \<notin> set p" using \<open>{1, 2, 5, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 1 p = 0" using nepostojanje by auto
  have "2 \<notin> set p" using \<open>{1, 2, 5, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 2 p = 0" using nepostojanje by auto
  have "50 \<notin> set p" using \<open>{1, 2, 5, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 50 p = 0" using nepostojanje by auto
  have "100 \<notin> set p" using \<open>{1, 2, 5, 50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 100 p = 0" using nepostojanje by auto

  have "novcanice p" "suma p = x" using \<open>optimalna_podela x p\<close> 
    unfolding optimalna_podela_def jeste_podela_def by auto


  then show "x \<le> 40"
  proof (cases "broj_y 10 p = 0")
    case True
    then have "suma p \<le> 40" using \<open>broj_y 1 p = 0\<close> \<open>broj_y 20 p \<le> 2\<close> \<open>broj_y 5 p = 0\<close>
    \<open>broj_y 1 p = 0\<close> \<open>broj_y 2 p = 0\<close> \<open>broj_y 50 p = 0\<close> \<open>broj_y 100 p = 0\<close>
     ukupno2 \<open>novcanice p\<close> by auto
    then show ?thesis using \<open>suma p = x\<close> by auto
  next
    case False
    then have "broj_y 20 p \<le> 1" using \<open>broj_y 10 p = 0 \<or> broj_y 20 p \<le> 1\<close> by auto
    then have "suma p \<le> 30" using \<open>broj_y 10 p \<le> 1\<close> \<open>broj_y 20 p \<le> 1\<close> \<open>broj_y 5 p = 0\<close>
    \<open>broj_y 1 p = 0\<close> \<open>broj_y 2 p = 0\<close> \<open>broj_y 50 p = 0\<close> \<open>broj_y 100 p = 0\<close>
     ukupno2 \<open>novcanice p\<close> by auto
    then show ?thesis using \<open>suma p = x\<close> by auto
  qed
qed

lemma Sa_1251020_najvise_49:
  "optimalna_podela x p \<and> {50, 100} \<inter> set p = {} \<longrightarrow> x \<le> 49"
  apply (rule impI)
  apply (erule conjE)
proof-
  assume "optimalna_podela x p" "{50, 100} \<inter> set p = {}"
  then have "broj_y 1 p \<le> 1" using Najvise_jedna_1 by auto
  have "broj_y 2 p \<le> 2" using \<open>optimalna_podela x p\<close> Najvise_dve_2 by auto
  have "\<not>(broj_y 1 p \<ge> 1 \<and> broj_y 2 p \<ge> 2)" using \<open>optimalna_podela x p\<close> 
        Nije_moguce_221 by auto
  then have "broj_y 1 p = 0 \<or> broj_y 2 p \<le> 1" by auto
  have "broj_y 5 p \<le> 1" using \<open>optimalna_podela x p\<close>  Najvise_jedna_5 by auto
  have "broj_y 10 p \<le> 1" using \<open>optimalna_podela x p\<close> Najvise_jedna_10 by auto
  have "broj_y 20 p \<le> 2" using \<open>optimalna_podela x p\<close> Najvise_dve_20 by auto
  have "\<not>(broj_y 10 p \<ge> 1 \<and> broj_y 20 p \<ge> 2)" using \<open>optimalna_podela x p\<close> 
        Nije_moguce_202010 by auto

  have "50 \<notin> set p" using \<open>{50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 50 p = 0" using nepostojanje by auto
  have "100 \<notin> set p" using \<open>{50, 100} \<inter> set p = {}\<close> by auto
  then have "broj_y 100 p = 0" using nepostojanje by auto

  have "novcanice p" "suma p = x" using \<open>optimalna_podela x p\<close> 
    unfolding optimalna_podela_def jeste_podela_def by auto


  then show "x \<le> 49"
    oops
qed


(* Cilj *)

lemma Gramziva_strategija:
  "optimalna_podela x (gramziva_podela x)"
  oops

end