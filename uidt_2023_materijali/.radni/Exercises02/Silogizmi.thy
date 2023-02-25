theory Silogizmi
  imports Main

begin

lemma Barbara:
"
(\<forall>x. Man x \<longrightarrow> Mortal x)
\<and>
(\<forall>x. Greek x \<longrightarrow> Man x)
\<longrightarrow>
(\<forall>x. Greek x \<longrightarrow> Mortal x)
"
  by auto

lemma Celarent:
"
(\<not>(\<exists>x. Reptile x \<and> Fur x))
\<and>
(\<forall>x. Snake x \<longrightarrow> Reptile x)
\<longrightarrow>
(\<not>(\<exists>x. Snake x \<and> Fur x))
"
  by auto

lemma Darii:
"
(\<forall>x. Rabbit x \<longrightarrow> Fur x)
\<and>
(\<exists>x. Pet x \<and> Rabbit x)
\<longrightarrow>
(\<exists>x. Pet x \<and> Fur x)
"
  by auto

lemma Ferio:
"
(\<not>(\<exists>x. Homework x \<longrightarrow> Fun x))
\<and>
(\<exists>x. Reading x \<and> Homework x)
\<longrightarrow>
(\<exists>x. Reading x \<and> \<not> Fun x)
"
  by auto

lemma Baroco:
"
(\<forall>x. Cat x \<longrightarrow> Mammal x)
\<and>
(\<exists>x. Pet x \<and> \<not>Mammal x)
\<longrightarrow>
(\<exists>x. Pet x \<and> \<not>Cat x)
"
  by auto

lemma Bocardo:
"
(\<exists>x. Cat x \<and> \<not>Pet x)
\<and>
(\<forall>x. Cat x \<longrightarrow> Mammal x)
\<longrightarrow>
(\<exists>x. Mammal x \<and> \<not>Pet x)
"
  by auto

lemma Barbari:
"
(\<forall>x. Man x \<longrightarrow> Mortal x)
\<and>
(\<forall>x. Greek x \<longrightarrow> Man x)
\<and>
(\<exists>x. Greek x)
\<longrightarrow>
(\<exists>x. Greek x \<and> Mortal x)
"
  by auto

lemma Celaront:
"
(\<not>(\<exists>x. Reptile x \<and> Fur x))
\<and>
(\<forall>x. Snake x \<longrightarrow> Reptile x)
\<and>
(\<exists>x. Snake x)
\<longrightarrow>
(\<exists>x. Snake x \<and> \<not>Fur x)
"
  by auto

lemma Camestros:
"
(\<forall>x. Horse x \<longrightarrow> Hooves x)
\<and>
(\<not>(\<exists>x. Human x \<and> Hooves x))
\<and>
(\<exists>x. Human x)
\<longrightarrow>
(\<exists>x. Human x \<and> \<not>Horse x)
"
  by auto

lemma Felapton:
"
(\<not>(\<exists>x. Flower x \<and> Animal x))
\<and>
(\<forall>x. Flower x \<longrightarrow> Plant x)
\<and>
(\<exists>x. Flower x)
\<longrightarrow>
(\<exists>x. Plant x \<and> \<not>Animal x)
"
  by auto

lemma Darapti:
"
(\<forall>x. Square x \<longrightarrow> Rectangle x)
\<and>
(\<forall>x. Square x \<longrightarrow> Rhombus x)
\<and>
(\<exists>x. Square x)
\<longrightarrow>
(\<exists>x. Rhombus x \<and> Rectangle x)
"
  by auto

end