
(*<*)
theory Vezbe07_resenja
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Isar dokazi u logici prvog reda.]\<close>

lemma 
  assumes "(\<exists> x. P x)"
      and "(\<forall> x. P x \<longrightarrow> Q x)"
    shows "(\<exists> x. Q x)"
proof -
  from assms(1) obtain x where "P x" by - (erule exE)
  moreover
  from assms(2) have "P x \<longrightarrow> Q x" by (erule_tac x="x" in allE)
  ultimately
  have "Q x" by - (erule impE, assumption)
  then show "(\<exists> x. Q x)" by (rule_tac x="x" in exI)
qed

lemma
  assumes "\<forall> c. Man c \<longrightarrow> Mortal c"
      and "\<forall> g. Greek g \<longrightarrow> Man g"
    shows "\<forall> a. Greek a \<longrightarrow> Mortal a"
proof
  fix Socrates
  show "Greek Socrates \<longrightarrow> Mortal Socrates"
  proof
    assume "Greek Socrates"
    moreover
    from assms(2) have "Greek Socrates \<longrightarrow> Man Socrates" 
      by (erule_tac x="Socrates" in allE)
    ultimately
    have "Man Socrates" by - (erule impE, assumption)
    moreover
    from assms(1) have "Man Socrates \<longrightarrow> Mortal Socrates" 
      by (erule_tac x="Socrates" in allE)
    ultimately
    show "Mortal Socrates" 
      by - (erule impE, assumption)
  qed
qed

text \<open>Dodatni primeri:\<close>

text \<open>Ako svaki konj ima potkovice;\\
      i ako ne postoji čovek koji ima potkovice;\\
      i ako znamo da postoji makar jedan čovek;\\
      dokazati da postoji čovek koji nije konj.\<close>

lemma
  assumes "\<forall> x. konj x \<longrightarrow> potkovice x"
      and "\<not> (\<exists> x. covek x \<and> potkovice x)"
      and "\<exists> x. covek x"
    shows "\<exists> x. covek x \<and> \<not> konj x"
proof -
  from assms(3) obtain x where "covek x" by auto
  have "konj x \<or> \<not> konj x" by auto
  then show "\<exists> x. covek x \<and> \<not> konj x"
  proof
    assume "konj x"
    moreover
    from assms(1) have "konj x \<longrightarrow> potkovice x" by auto
    ultimately 
    have "potkovice x" by auto
    with \<open>covek x\<close> have "covek x \<and> potkovice x" by auto
    then have "\<exists> x. covek x \<and> potkovice x" by auto
    with assms(2) have False by auto
    then show "\<exists> x. covek x \<and> \<not> konj x" by auto
  next
    assume "\<not> konj x"
    with \<open>covek x\<close> have "covek x \<and> \<not> konj x" by auto
    then show "\<exists> x. covek x \<and> \<not> konj x" by auto
  qed
qed

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Pravilo ccontr i classical.]\<close>

text \<open>Dokazati u Isar jeziku naredna tvrđenja pomoću pravila \<open>ccontr\<close>.\<close>

lemma "\<not> (A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
proof
  assume "\<not> (A \<and> B)"
  show "\<not> A \<or> \<not> B"
  proof (rule ccontr)
    assume "\<not> (\<not> A \<or> \<not> B)"
    have "A \<and> B"
    proof
      show A
      proof (rule ccontr)
        assume "\<not> A"
        then have "\<not> A \<or> \<not> B" 
          by (rule disjI1)
        with \<open>\<not> (\<not> A \<or> \<not> B)\<close> show False 
          by - (erule notE, assumption)
      qed
    next 
      show B
      proof (rule ccontr)
        assume "\<not> B"
        then have "\<not> A \<or> \<not> B" 
          by (rule disjI2)
        with \<open>\<not> (\<not> A \<or> \<not> B)\<close> show False 
          by - (erule notE, assumption)
      qed
    qed
    with \<open>\<not> (A \<and> B)\<close> show False 
      by - (erule notE, assumption)
  qed
qed

text \<open>Dodatni primer:\<close>

lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
proof 
  assume "(P \<longrightarrow> Q) \<longrightarrow> P"
  show P
  proof (rule ccontr)
    assume "\<not> P"
    have "P \<longrightarrow> Q"
    proof
      assume P
      with \<open>\<not> P\<close> have False by auto
      then show Q by auto
    qed
    with \<open>(P \<longrightarrow> Q) \<longrightarrow> P\<close> have "P" by auto
    with \<open>\<not> P\<close> show False by auto
  qed
qed

text \<open>Dokazati u Isar jeziku naredna tvrđenja pomoću pravila \<open>classical\<close>.\<close>

lemma "P \<or> \<not> P"
proof (rule classical)
  assume "\<not> (P \<or> \<not> P)"
  show "P \<or> \<not> P"
  proof (rule disjI1)
    show P
    proof (rule classical)
      assume "\<not> P"
      then have "P \<or> \<not> P" 
        by (rule disjI2)
      with \<open>\<not> (P \<or> \<not> P)\<close> have False 
        by - (erule notE, assumption)
      then show P using FalseE[of P] 
        by - (assumption)
    qed
  qed
qed

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Logčki lavirinti.]\<close>

text \<open>Svaka osoba daje potvrdan odgovor na pitanje: \<open>Da li si ti vitez?\<close>\<close>

lemma no_one_admits_knave:
  assumes "k \<longleftrightarrow> (k \<longleftrightarrow> ans)"
    shows ans
proof (cases k)
  assume k
  with assms have "k \<longleftrightarrow> ans"  by auto
  with \<open>k\<close> show ?thesis by auto
next
  assume "\<not> k"
  with assms have "\<not> (k \<longleftrightarrow> ans)" by auto
  then have "\<not> k \<longrightarrow> ans" by auto
  with \<open>\<not> k\<close> show ?thesis by auto
qed

text \<open>Abercrombie je sreo tri stanovnika, koje ćemo zvati A, B i C. 
      Pitao je A: Jesi li ti vitez ili podanik?
      On je odgovorio, ali tako nejasno da Abercrombie nije mogao shvati 
      što je rekao. 
      Zatim je upitao B: Šta je rekao? 
      B odgovori: Rekao je da je podanik.
      U tom trenutku, C se ubacio i rekao: Ne verujte u to; to je laž! 
      Je li C bio vitez ili podanik?\<close>

lemma Smullyan_1_1:
  assumes "kA \<longleftrightarrow> (kA \<longleftrightarrow> ansA)"
      and "kB \<longleftrightarrow> \<not> ansA"
      and "kC \<longleftrightarrow> \<not> kB"
    shows kC
proof -
  from assms(1) have ansA using no_one_admits_knave[of kA ansA] by simp
  with assms(2) have "\<not> kB" by simp
  with assms(3) show kC by simp
qed

text \<open>Prema drugoj verziji priče, 
      Abercrombie nije pitao A da li je on vitez ili podanik 
      (jer bi unapred znao koji će odgovor dobiti), 
      već je pitao A koliko od njih trojice su bili vitezovi. 
      Opet je A odgovorio nejasno, pa je Abercrombie upitao B što je A rekao. 
      B je tada rekao da je A rekao da su tačno njih dvojica podanici. 
      Tada je, kao i prije, C tvrdio da B laže. 
      Je li je sada moguće utvrditi da li je C vitez ili podanik?\<close>

definition exactly_two :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "exactly_two A B C \<longleftrightarrow> ((A \<and> B) \<or> (A \<and> C) \<or> (B \<and> C)) \<and> \<not> (A \<and> B \<and> C)"

lemma Smullyan_1_2:
  assumes "kB \<longleftrightarrow> (kA \<longleftrightarrow> exactly_two (\<not> kA) (\<not> kB) (\<not> kC))"
      and "kC \<longleftrightarrow> \<not> kB"
    shows "kC"
proof(cases kC)
  case True
  then show ?thesis by auto
next
  case False
  with assms(2) have "kB" by auto
  with assms(1) have *:"kA \<longleftrightarrow> exactly_two (\<not> kA) (\<not> kB) (\<not> kC)" by auto
  have False
  proof (cases kA)
    case True
    with * have "exactly_two (\<not> kA) (\<not> kB) (\<not> kC)" by auto
    with \<open>kA\<close> \<open>kB\<close> \<open>\<not> kC\<close> show ?thesis using exactly_two_def by auto
  next
    case False
    with * have "\<not> exactly_two (\<not> kA) (\<not> kB) (\<not> kC)" by auto
    with \<open>\<not> kA\<close> \<open>kB\<close> \<open>\<not> kC\<close> show ?thesis using exactly_two_def by auto
  qed
  then show ?thesis by auto
qed

text \<open>Dodatni primer:\<close>

text \<open>Abercrombie je sreo samo dva stanovnika A i B. 
      A je izjavio: Obojica smo podanici. 
      Da li možemo da zaključimo šta je A a šta je B?\<close>

lemma Smullyan_1_3:
  assumes "kA \<longleftrightarrow> \<not> kA \<and> \<not> kB"
  shows "\<not> kA \<and> kB"
proof (cases kA)
  case True
  with assms have "\<not> kA \<and> \<not> kB" by auto
  then have "\<not> kA" by auto
  with \<open>kA\<close> have False by auto
  then show ?thesis by auto
next
  case False
  with assms have "\<not> (\<not> kA \<and> \<not> kB)" by auto
  then have "kA \<or> kB" by auto
  then show ?thesis
  proof
    assume kA
    with \<open>\<not> kA\<close> have False by auto
    then show ?thesis by auto
  next
    assume kB
    with \<open>\<not> kA\<close> show ?thesis by auto
  qed
qed

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
