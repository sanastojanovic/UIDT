theory Formule
  imports Main

begin

term "length x"
term "3"
term "3::nat"
term "a \<union> b"
term "f x"

term "A \<and> B"
term "P x \<and> Q x"
term "(\<and>)"

lemma "A \<and> A \<longrightarrow> A \<and> A"
  by auto

lemma "A \<and> B \<longrightarrow> B \<and> A"
  by auto

lemma "A \<longrightarrow> A \<or> B \<or> C \<or> D"
  by auto

lemma "A \<longrightarrow> A"
  by auto

lemma "((\<forall>x. Laze x \<longrightarrow> Krade x) \<and> (\<exists>x. Laze x)) \<longrightarrow> (\<exists>x. Krade x)"
  by auto

lemma 
"
(
(\<forall>x. Radi x \<longrightarrow> Ima x \<or> Trosi x) \<and> 
(\<forall>x. Ima x \<longrightarrow> Peva x) \<and> 
(\<forall>x. Trosi x \<longrightarrow> Peva x)
) 
\<longrightarrow>
(\<forall>x. Radi x \<longrightarrow> Peva x)
"
  by auto

lemma 
"
(\<forall>X.\<forall>Y. Prijatelj X Y \<longrightarrow> Prijatelj Y X)
\<and>
(\<forall>X.\<forall>Y. Prijatelj X Y \<longrightarrow> Voli X Y)
\<and>
(\<not>(\<exists>X.\<exists>Y. Voli X Y \<and> Povredio X Y))
\<and>
(\<exists>X.\<exists>Y. Povredio Y X \<and> Prijatelj Y X)
\<longrightarrow> False
"
  by auto

lemma 
"
(\<forall>x. Leti x \<longrightarrow> Krila x \<and> Lagano x)
\<and>
(\<forall>x. Pliva x \<longrightarrow> \<not> Krila x)
\<longrightarrow>
(\<forall>x. Pliva x \<longrightarrow> \<not> Leti x)
"
  by auto

lemma
"
(\<exists>cipela. \<forall>trenutak. \<forall>noga. Odgovara cipela trenutak noga)
\<longrightarrow>
(\<forall>noga. \<exists>cipela. \<exists>trenutak. Odgovara cipela trenutak noga)
\<and>
(\<forall>noga. \<exists>trenutak. \<exists>cipela. Odgovara cipela trenutak noga)
"
  by auto

lemma
"
(\<forall>x.\<forall>y.\<exists>z. Brat x y \<longrightarrow> Roditelj x z \<and> Roditelj y z)
\<and>
(\<forall>x.\<forall>y. Roditelj x y \<longrightarrow> Stariji y x)
\<and>
(\<exists>x.\<exists>y. Brat x y)
\<and>
(\<not>(\<exists>x.\<exists>y. Stariji x y))
\<longrightarrow> 
False
"
  by auto

lemma
"
(\<forall>x. Decak x \<longrightarrow> Igra x)
\<and>
(\<forall>x. Devojcica x \<longrightarrow> Igra x)
\<and>
(\<forall>x. Dete x \<longrightarrow> Decak x \<or> Devojcica x)
\<longrightarrow>
(\<forall>x. Dete x \<longrightarrow> Igra x)
"
  by auto

end