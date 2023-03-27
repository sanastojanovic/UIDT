
(*<*)
theory Vezbe06
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Svojstva funkcija]\<close>

text \<open>Pokazati da je slika unije, unija pojedinačnih slika.\\
      \<open>Savet\<close>: Razmotriti teoreme \<open>image_def\<close> i \<open>vimage_def\<close>.\<close>

lemma image_union:
  shows "f ` (A \<union> B) = f ` A \<union> f ` B"
(*<*) oops (*>*)

text \<open>Neka je funkcija \<open>f\<close> injektivna. 
      Pokazati da je slika preseka, presek pojedinačnih slika.\\
      \<open>Savet\<close>: Razmotriti teoremu \<open>inj_def\<close>.\<close>

lemma image_inter: 
  assumes "inj f"
  shows "f ` (A \<inter> B) = f ` A \<inter> f ` B"
(*<*) oops (*>*)

text \<open>\<open>Savet\<close>: Razmotriti teoremu \<open>surj_def\<close> i \<open>surjD\<close>.\<close>

lemma surj_image_vimage:
  assumes "surj f"
  shows "f ` (f -` A) = A"
(*<*) oops (*>*)

text \<open>Pokazati da je kompozicija injektivna 
      ako su pojedinačne funkcije injektivne.\\
      \<open>Savet\<close>: Razmotrite teoremu \<open>inj_eq\<close>.\<close>

lemma comp_inj:
  assumes "inj f"
  assumes "inj g"
  shows "inj (f \<circ> g)"
(*<*) oops (*>*)

lemma
  assumes "inj f"
  shows "x \<in> A \<longleftrightarrow> f x \<in> f ` A"
(*<*) oops (*>*)


lemma inj_vimage_image:
  assumes "inj f"
  shows "f -` (f ` A) = A"
(*<*) oops (*>*)

text \<open>Kompozicija je surjekcija
      ako su pojedinačne funkcije surjekcije.\<close>

lemma comp_surj:
  assumes "surj f"
  assumes "surj g"
  shows "surj (f \<circ> g)"
(*<*) oops (*>*)

lemma vimage_compl: 
  shows "f -` ( - B) = - (f -` B)"
(*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

(*<*)
end
(*>*)
