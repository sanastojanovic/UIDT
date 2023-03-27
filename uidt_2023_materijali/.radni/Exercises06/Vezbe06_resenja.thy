
(*<*)
theory Vezbe06_resenja
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Svojstva funkcija]\<close>

text \<open>Pokazati da je slika unije, unija pojedinačnih slika.\\
      \<open>Savet\<close>: Razmotriti teoreme \<open>image_def\<close> i \<open>vimage_def\<close>.\<close>

lemma image_union:
  shows "f ` (A \<union> B) = f ` A \<union> f ` B"
proof
  show "f ` (A \<union> B) \<subseteq> f ` A \<union> f ` B"
  proof
    fix y
    assume "y \<in> f ` (A \<union> B)"
    then have "\<exists> x. x \<in> A \<union> B \<and> f x = y" by auto
    then obtain x where "x \<in> A \<union> B" "f x = y" by auto
    then have "x \<in> A \<or> x \<in> B" by auto
    then have "f x \<in> f ` A \<or> f x \<in> f ` B" by auto
    with \<open>f x = y\<close> show "y \<in> f ` A \<union> f ` B" by auto
  qed
next
  show "f ` A \<union> f ` B \<subseteq> f ` (A \<union> B)"
  proof
    fix y
    assume "y \<in> f ` A \<union> f ` B"
    then have "y \<in> f ` A \<or> y \<in> f ` B" by simp
    then show "y \<in> f ` (A \<union> B)"
    proof
      assume "y \<in> f ` A"
      then have "\<exists> x. x \<in> A \<and> f x = y" by auto
      then obtain x where "x \<in> A" "f x = y" by auto
      then have "x \<in> A \<union> B" by simp
      then have "f x \<in> f ` (A \<union> B)" by simp
      with \<open>f x = y\<close> show "y \<in> f ` (A \<union> B)" by auto 
    next
      assume "y \<in> f ` B"
      then have "\<exists> x. x \<in> B \<and> f x = y" by auto
      then obtain x where "x \<in> B" "f x = y" by auto
      then have "x \<in> A \<union> B" by simp
      then have "f x \<in> f ` (A \<union> B)" by simp
      with \<open>f x = y\<close> show "y \<in> f ` (A \<union> B)" by auto
    qed
  qed
qed

text \<open>Neka je funkcija \<open>f\<close> injektivna. 
      Pokazati da je slika preseka, presek pojedinačnih slika.\\
      \<open>Savet\<close>: Razmotriti teoremu \<open>inj_def\<close>.\<close>

lemma image_inter: 
  assumes "inj f"
  shows "f ` (A \<inter> B) = f ` A \<inter> f ` B"
proof
  show "f ` (A \<inter> B) \<subseteq> f ` A \<inter> f ` B"
  proof
    fix y
    assume "y \<in> f ` (A \<inter> B)"
    then have "\<exists> x \<in> A \<inter> B. f x = y" by auto
    then obtain x where "x \<in> A \<inter> B" "f x = y" by auto
    then have "x \<in> A \<and> x \<in> B" by auto
    then have "f x \<in> f ` A \<and> f x \<in> f ` B" by auto
    with \<open>f x = y\<close> show "y \<in> f ` A \<inter> f ` B" by auto
  qed
next
  show "f ` A \<inter> f ` B \<subseteq> f ` (A \<inter> B)"
  proof
    fix y
    assume "y \<in> f ` A \<inter> f ` B"
    then have "y \<in> f ` A" "y \<in> f ` B" by auto
    from \<open>y \<in> f ` A\<close> obtain xa where "xa \<in> A" "f xa = y" by auto
    moreover
    from \<open>y \<in> f ` B\<close> obtain xb where "xb \<in> B" "f xb = y" by auto
    ultimately 
    have "xa = xb" using assms by (simp add: inj_def)
    with \<open>xa \<in> A\<close> have "xb \<in> A" by auto
    with \<open>xb \<in> B\<close> have "xb \<in> A \<and> xb \<in> B" by auto
    then have "xb \<in> A \<inter> B" by auto
    then have "f xb \<in> f ` (A \<inter> B)" by auto
    with \<open>f xb = y\<close> show "y \<in> f ` (A \<inter> B)" by auto
  qed
qed

text \<open>\<open>Savet\<close>: Razmotriti teoremu \<open>surj_def\<close> i \<open>surjD\<close>.\<close>

lemma surj_image_vimage:
  assumes "surj f"
  shows "f ` (f -` B) = B"
proof
  show "f ` f -` B \<subseteq> B"
  proof
    fix y
    assume "y \<in> f ` f -` B"
    then obtain x where "x \<in> f -` B" "f x = y" by auto
    then have "f x \<in> B" by auto
    with \<open>f x = y\<close> show "y \<in> B" by auto
  qed
next
  show "B \<subseteq> f ` f -` B"
  proof
    fix y
    assume "y \<in> B"
    with assms obtain x where "f x = y" using surjD by metis
    with \<open>y \<in> B\<close> have "x \<in> f -` B" by auto
    then have "f x \<in> f ` (f -` B)" by auto
    with \<open>f x = y\<close> show "y \<in> f ` f -` B" by auto
  qed
qed

text \<open>Pokazati da je kompozicija injektivna 
      ako su pojedinačne funkcije injektivne.\\
      \<open>Savet\<close>: Razmotrite teoremu \<open>inj_eq\<close>.\<close>

lemma comp_inj:
  assumes "inj f"
  assumes "inj g"
  shows "inj (f \<circ> g)"
proof
  fix x y
  assume "(f \<circ> g) x = (f \<circ> g) y"
  then have "f (g x) = f (g y)" by auto
  with \<open>inj f\<close> have "g x = g y" by (simp add: inj_eq)
  with \<open>inj g\<close> show "x = y" by (simp add: inj_eq)
qed

lemma
  assumes "inj f"
  shows "x \<in> A \<longleftrightarrow> f x \<in> f ` A"
proof
  assume "x \<in> A"
  then show "f x \<in> f ` A" by auto
next
  assume "f x \<in> f ` A"
  then obtain x' where "x' \<in> A" "f x = f x'" by auto
  with \<open>inj f\<close> have "x = x'" by (simp add: inj_eq)
  with \<open>x' \<in> A\<close> show "x \<in> A" by auto
qed

lemma inj_vimage_image:
  assumes "inj f"
  shows "f -` (f ` A) = A"
proof
  show "f -` f ` A \<subseteq> A"
  proof
    fix x
    assume "x \<in> f -` (f ` A)"
    then obtain y where "y \<in> f ` A" "f x = y" by auto
    then obtain x' where "x' \<in> A" "f x' = y" by auto
    with \<open>f x = y\<close> have "f x = f x'" by auto
    with assms have "x = x'" by (simp add: inj_eq)
    with \<open>x' \<in> A\<close> show "x \<in> A" by auto
  qed
next
  show "A \<subseteq> f -` f ` A"
  proof
    fix x
    assume "x \<in> A"
    then have "f x \<in> f ` A" by auto
    then show "x \<in> f -` f ` A" by auto
  qed
qed

text \<open>Kompozicija je surjekcija
      ako su pojedinačne funkcije surjekcije.\<close>

lemma comp_surj:
  assumes "surj f"
  assumes "surj g"
  shows "surj (f \<circ> g)"
  unfolding surj_def
proof
  fix z
  from \<open>surj f\<close> obtain y where \<open>z = f y\<close> by auto
  moreover
  from \<open>surj g\<close> obtain x where \<open>y = g x\<close> by auto
  ultimately
  have "z = f (g x)" by auto
  then show "\<exists>x. z = (f \<circ> g) x" by auto
qed

lemma vimage_compl: 
  shows "f -` (- B) = - (f -` B)"
proof
  show "f -` (- B) \<subseteq> - f -` B"
  proof
    fix x
    assume "x \<in> f -` (- B)"
    then obtain y where "y \<in> - B" "f x = y" by auto
    then have "y \<notin> B" by auto
    with \<open>f x = y\<close> have "f x \<notin> B" by auto
    then have "x \<notin> f -` B" by auto
    then show "x \<in> - f -` B" by auto
  qed
next
  show "- f -` B \<subseteq> f -` (- B)"
  proof
    fix x
    assume "x \<in> - f -` B"
    then have "x \<notin> f -` B" by auto
    then have "f x \<notin> B" by auto
    then have "f x \<in> -B" by auto
    then show "x \<in> f -` (- B)" by auto
  qed
qed

text_raw \<open> \end{exercise} \<close>

(*<*)
end
(*>*)
