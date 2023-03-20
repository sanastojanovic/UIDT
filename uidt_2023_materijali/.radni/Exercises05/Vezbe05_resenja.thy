
(*<*)
theory Vezbe05_resenja 
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Algebra skupova]\<close>

text \<open>Diskutovati o sledećim termovima:\<close>

term "{1, 2, 3}"
term "{1::nat, 2, 3}"
term "(\<in>)"
term "(\<inter>)"
term "(\<union>)"
term "(\<union>) A"
term "A \<union> B"
term "(A::'a set) - B"

text_raw \<open> \end{exercise} \<close>


text_raw \<open>\begin{exercise}[subtitle=Isar dokazi]\<close>

text \<open>Pokazati sledeća tvrđenja o skupovima pomoću jezika Isar.\<close>

text \<open>\<open>Napomena\<close>: Dozvoljeno je korišćenje samo \<open>simp\<close> metode za
                  dokazivanje pojedinačnih koraka.\<close>

lemma "- (A \<union> B) = - A \<inter> - B"
proof
  show "- (A \<union> B) \<subseteq> - A \<inter> - B"
  proof
    fix x
    assume "x \<in> - (A \<union> B)"
    then have "x \<notin> A \<union> B" by simp
    then have "x \<notin> A \<and> x \<notin> B" by simp
    then have "x \<in> - A \<and> x \<in> - B" by simp
    then show "x \<in> - A \<inter> - B" by simp
  qed
next
  show "- A \<inter> - B \<subseteq> - (A \<union> B)"
  proof
    fix x
    assume "x \<in> - A \<inter> - B"
    then have "x \<in> - A \<and> x \<in> - B" by simp
    then have "x \<notin> A \<and> x \<notin> B" by simp
    then have "x \<notin> A \<union> B" by simp
    then show "x \<in> - (A \<union> B)" by simp
  qed
qed

text \<open>\<open>Savet\<close>: Iskoristiti @{text "find_theorems _ \<or> _ \<longleftrightarrow> _ \<or> _"} 
               za pronalaženje odgovarajuće teoreme.\<close>

lemma "A \<union> B = B \<union> A"
proof
  show "A \<union> B \<subseteq> B \<union> A"
  proof
    fix x
    assume "x \<in> A \<union> B"
    then have "x \<in> A \<or> x \<in> B" by simp
    then have "x \<in> B \<or> x \<in> A" using disj_commute[of "x \<in> A" "x \<in> B"] by simp
    then show "x \<in> B \<union> A" by simp
  qed
next
  show "B \<union> A \<subseteq> A \<union> B"
  proof
    fix x
    assume "x \<in> B \<union> A"
    then have "x \<in> B \<or> x \<in> A" by simp
    then have "x \<in> A \<or> x \<in> B" using disj_commute[of "x \<in> A" "x \<in> B"] by simp
    then show "x \<in> A \<union> B" by simp
  qed
qed

text \<open>\<open>Savet\<close>: Iskoristiti aksiomu isključenja trećeg @{text "A \<or> \<not>A"}
               u kontekstu operacije pripadanja @{text "(\<in>) :: 'a \<Rightarrow> 'a set \<Rightarrow> bool"}.\<close>

lemma "A \<union> (B \<inter> C) = (A \<union> B) \<inter> (A \<union> C)" (is "?left = ?right")
proof
  show "?left \<subseteq> ?right"
  proof
    fix x
    assume "x \<in> ?left"
    then have "x \<in> A \<or> x \<in> B \<inter> C" by simp
    then show "x \<in> ?right"
    proof
      assume "x \<in> A"
      then have "x \<in> A \<union> B \<and> x \<in> A \<union> C" by simp
      then show "x \<in> ?right" by simp
    next
      assume "x \<in> B \<inter> C"
      then have "x \<in> B \<and> x \<in> C" by simp
      then have "x \<in> A \<union> B \<and> x \<in> A \<union> C" by simp
      then show "x \<in> ?right" by simp
    qed
  qed
next
  show "?right \<subseteq> ?left"
  proof
    fix x
    assume "x \<in> ?right"
    then have *: "x \<in> A \<union> B \<and> x \<in> A \<union> C" by simp
    have "x \<in> A \<or> x \<notin> A" by simp
    then show "x \<in> ?left"
    proof
      assume "x \<in> A"
      then show "x \<in> ?left" by simp
    next
      assume "x \<notin> A"
      from this and * have "x \<in> B \<and> x \<in> C" by simp
      then have "x \<in> B \<inter> C" by simp
      then show "x \<in> ?left" by simp
    qed
  qed
qed

lemma "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)" (is "?left = ?right")
proof
  show "?left \<subseteq> ?right"
  proof
    fix x
    assume "x \<in> ?left"
    then have *: "x \<in> A \<and> x \<in> B \<union> C" by simp
    then have "x \<in> A" by simp
    from * have "x \<in> B \<union> C" by simp
    then have "x \<in> B \<or> x \<in> C" by simp
    from this and \<open>x \<in> A\<close> have "x \<in> A \<inter> B \<or> x \<in> A \<inter> C" by simp
    then show "x \<in> ?right" by simp
  qed
next
  show "?right \<subseteq> ?left"
  proof
    fix x
    assume "x \<in> ?right"
    then have "x \<in> A \<inter> B \<or> x \<in> A \<inter> C" by simp
    then show "x \<in> ?left"
    proof
      assume "x \<in> A \<inter> B"
      then have "x \<in> A \<and> x \<in> B" by simp
      then have "x \<in> A \<and> x \<in> B \<union> C" by simp
      then show "x \<in> ?left" by simp
    next
      assume "x \<in> A \<inter> C"
      then have "x \<in> A \<and> x \<in> C" by simp
      then have "x \<in> A \<and> x \<in> B \<union> C" by simp
      then show "x \<in> ?left" by simp
    qed
  qed
qed

lemma "A - (B \<inter> C ) = (A - B) \<union> (A - C )" (is "?left = ?right")
proof
  show "?left \<subseteq> ?right"
  proof
    fix x
    assume "x \<in> ?left"
    then have *: "x \<in> A \<and> x \<notin> B \<inter> C" by simp
    then have "x \<in> A" by simp
    from * have "x \<notin> B \<inter> C" by simp
    then have "x \<notin> B \<or> x \<notin> C" by simp
    then show "x \<in> ?right"
    proof
      assume "x \<notin> B"
      with \<open>x \<in> A\<close> have "x \<in> A - B" by simp
      then show "x \<in> ?right" by simp
    next
      assume "x \<notin> C"
      with \<open>x \<in> A\<close> have "x \<in> A - C" by simp
      then show "x \<in> ?right" by simp
    qed
  qed
next
  show "?right \<subseteq> ?left"
  proof
    fix x
    assume "x \<in> ?right"
    then have "x \<in> A - B \<or> x \<in> A - C" by simp
    then show "x \<in> ?left"
    proof
      assume "x \<in> A - B"
      then have "x \<in> A \<and> x \<notin> B" by simp
      then have "x \<in> A \<and> x \<notin> B \<inter> C" by simp
      then show "x \<in> ?left" by simp
    next
      assume "x \<in> A - C"
      then have "x \<in> A \<and> x \<notin> C" by simp
      then have "x \<in> A \<and> x \<notin> B \<inter> C" by simp
      then show "x \<in> ?left" by simp
    qed
  qed
qed

text_raw \<open> \end{exercise} \<close>

(*<*)
end
(*>*)
