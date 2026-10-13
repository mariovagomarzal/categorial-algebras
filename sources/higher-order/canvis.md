# Canvis a `main.tex`: resolució dels comentaris en roig

Data: 2026-10-13. Fitxer: `sources/higher-order/main.tex`.

Hi havia set comentaris en roig (`\textcolor{red}{…}`); un vuité, «Subseccions
extra», ja l'havies esborrat tu abans de començar. Tots set s'han resolt i
eliminat. Totes les etiquetes LaTeX existents es conserven (el pla de
`sources/higher-order/*.toml` hi fa referència) i se n'han afegit de noves.
El document compila sense errors ni referències indefinides (pdflatex + bibtex).

Al final hi ha la llista de **decisions que has de revisar**.

---

## 1. Derivors generalitzats (`SGenDerivors`)

**Comentari.** No volem sorts ordenats ni predicats; treballem amb
E-equacions, no amb fórmules. La $d_{\mathbf{w},s}$ de l'apartat 3 ha de
correspondre amb la $d$ de la Definició `DDerivor`. Les paraules es denoten
$\mathbf{s}$. Un derivor generalitzat és una tripla $(\varphi, D, d)$ amb
$(\varphi,d)$ un derivor i $D$ un conjunt d'E-equacions per a cada sort.

**Què he fet.**

- He afegit un paràgraf de notació, que també fan servir les seccions 5 i 6:
  - $v^{\mathbf{t}}_{j}$ és la variable de $\downarrow\mathbf{t}$ corresponent a la lletra $j$.
  - $\mathrm{Eq}_{\Lambda}(X)=\coprod_{t}\mathrm{T}_{\Lambda}(X)^2_t$ és el conjunt de les E-equacions.
  - $\mathbf{B}\models\mathcal{E}[b]$ indica satisfacció sota una valoració; una família $\mathbf{b}\in B_{\mathbf{t}}$ s'identifica amb una valoració.
  - $f^{\sharp}[\mathcal{E}]$ és la substitució aplicada a un conjunt d'equacions.
- He reescrit `DGeneralDerivor`:
  - Un derivor generalitzat és $(\varphi,D,d)$, on $(\varphi,d)$ és un derivor en el sentit de `DDerivor` i $D_s\subseteq\mathrm{Eq}_\Lambda(\downarrow(\varphi(s)))$ són E-equacions en l'única variable $v^{\varphi(s)}_0$.
  - Defineix també $D_{\mathbf{s}}$ per a paraules: les condicions de cada lletra, reanomenades a la variable corresponent.
- He explicat la correspondència amb [LG18]: $D_s$ correspon a $\Delta_s(x)$, i $d_{\mathbf{s},s}(\sigma)$ correspon a $\Phi^\sigma$. Tot derivor és el derivor generalitzat $(\varphi,\varnothing,d)$.
- He afegit la nova Observació `RGenDerivorSem`, sobre la semàntica pretesa:
  - L'àlgebra $\mathbf{B}$ es restringeix als subconjunts $B^D_s$.
  - Perquè això done una $\Sigma$-àlgebra cal una **condició de clausura**. No l'he posada a la definició, perquè el comentari no la demanava. Apareix en forma sintàctica a la secció 6, com a condició (GEP1).

## 2. ep-derivors (`SEpDerivors`)

**Comentari.** Denotar una ep-signatura per $(S,\Sigma,\mathrm{def}^{\mathbf{\Sigma}})$.
Completar formalment $\mathrm{deft}^{\mathbf{\Sigma}}$ i l'operador de
conseqüència semàntica $\mathrm{Cn}$. Corregir la definició d'ep-derivor
tenint en compte el comentari que la seguia («I am not sure that this is the
correct definition…»).

**Què he fet** (la secció s'ha reescrit sencera):

- **`DEpSignature`** (nova): defineix l'ep-signatura $(S,\Sigma,\mathrm{def}^{\mathbf{\Sigma}})$ amb $\mathrm{def}^{\mathbf{\Sigma}}(\sigma)\subseteq\mathrm{Eq}_\Sigma(\downarrow\mathbf{s})$, el conjunt $A_{\mathrm{def}(\sigma)}$, les ep-àlgebres i la categoria $\mathsf{PAlg}(\mathbf{\Sigma})$. També corregeix les errades del text antic: $\mathbf{w}\to\mathbf{s}$ i «ordred». Una signatura total és el cas $\mathrm{def}=\varnothing$.
- **`RSubst`** (nova): lema de substitució per a àlgebres parcials. Només val quan els termes substituïts estan definits. Aquesta restricció és la causa de la correcció del punt 4 de més avall.
- **`DDeft`** (nova): $\mathrm{deft}^{\mathbf{\Sigma}}$ es defineix per recursió algebraica:
  $\mathrm{deft}(x)=\varnothing$ i
  $\mathrm{deft}(\sigma(P_j)_j)=\bigcup_j\mathrm{deft}(P_j)\cup(P_j)_j^{\sharp}[\mathrm{def}(\sigma)]$.
- **`LDeft`** (nou lema, amb prova): en una ep-àlgebra, $P^{\mathbf{A}}[a]$ està definit si i només si $\mathbf{A}\models\mathrm{deft}(P)[a]$. Aquesta és la justificació de $\mathrm{deft}$.
- **`DCn`** (nova): $\mathrm{Cn}^{\mathbf{\Sigma}}_X(\mathcal{E})$ és el conjunt de les E-equacions que valen en tota ep-àlgebra i sota tota valoració que satisfà $\mathcal{E}$. He afegit un paràgraf que diu que és un operador de clausura i que $\mathrm{Cn}(\mathcal{E})=\mathrm{Cn}(\mathcal{E}')$ si i només si $\mathcal{E}$ i $\mathcal{E}'$ tenen els mateixos models.
- **$\mathbf{d}^{\ast}(\mathbf{B})$**: la $\Sigma$-àlgebra parcial que s'obté interpretant cada $\sigma$ com l'operació terme parcial $d(\sigma)^{\mathbf{B}}$.
- **`DTranslation`** (nova) i **`LTranslation`** (nou lema, amb prova): la traducció $\mathrm{tr}_{\mathbf{d}}$ compleix que $\mathbf{d}^{\ast}(\mathbf{B})\models\mathcal{E}[\mathbf{b}]$ si i només si $\mathbf{B}\models\mathrm{tr}_{\mathbf{d}}[\mathcal{E}][\mathbf{b}]$. Vegeu el punt 4 de més avall.
- **`DDerivorEP`** (corregida). Abans era una còpia literal de `DDerivor`. Ara diu que un ep-derivor és un derivor tal que, per a cada $\sigma$,
  $$\mathrm{Cn}^{\mathbf{\Lambda}}(\mathrm{tr}_{\mathbf{d}}[\mathrm{def}^{\mathbf{\Sigma}}(\sigma)])=\mathrm{Cn}^{\mathbf{\Lambda}}(\mathrm{deft}^{\mathbf{\Lambda}}(d_{\mathbf{s},s}(\sigma))).$$
- **`PEpDerivorFunctor`** (nova, amb prova): $\mathbf{d}$ és un ep-derivor **si i només si** $\mathbf{d}^{\ast}$ envia $\mathbf{\Lambda}$-àlgebres a $\mathbf{\Sigma}$-àlgebres. En aquest cas $\mathbf{d}^{\ast}$ és un functor $\mathsf{PAlg}(\mathbf{\Lambda})\to\mathsf{PAlg}(\mathbf{\Sigma})$.
- **`REpDerivor`** (nova): substitueix el paràgraf «I am not sure…» i explica les correccions.

**Les correccions a la definició antiga, i per què:**

1. **Inclusió → igualtat.** La inclusió
   $d^\sharp\times d^\sharp[\mathrm{def}(\sigma)]\subseteq\mathrm{Cn}(\mathrm{def}(d^\sharp(\sigma)))$
   només garanteix que el domini de $d(\sigma)^{\mathbf{B}}$ està contingut en el conjunt de les famílies que satisfan $\mathrm{def}(\sigma)$. L'operació podria quedar indefinida on hauria d'estar definida, i aleshores $\mathbf{d}^*(\mathbf{B})$ no seria una ep-àlgebra. La igualtat de conseqüències, que és la condició de Reichel, és **exactament** la que fa que $\mathbf{d}^*$ siga un functor; ho prova `PEpDerivorFunctor`. Això confirma la sospita del comentari.
2. **$\mathrm{def}(d^\sharp(\sigma))\to\mathrm{deft}^{\mathbf{\Lambda}}(d_{\mathbf{s},s}(\sigma))$.** $d(\sigma)$ és un terme, i cal $\mathrm{deft}$, no $\mathrm{def}$.
3. **$d^\sharp_{\mathbf{s},s}\to d^\sharp$ en totes les components.** Les equacions de $\mathrm{def}(\sigma)$ poden ser de qualsevol sort, no només de $s$.
4. **$d^\sharp\times d^\sharp\to\mathrm{tr}_{\mathbf{d}}$** (correcció nova, no demanada al comentari). Si $d(\sigma)$ no conté alguna variable, per exemple $d(\sigma)=v_0$ per a un $\sigma$ binari, aleshores $d^\sharp(\sigma(P_0,P_1))=d^\sharp(P_0)$ pot estar definit en $\mathbf{B}$ encara que $P_1$ no ho estiga en $\mathbf{d}^*(\mathbf{B})$. Per tant, $(d^\sharp P,d^\sharp Q)$ no expressa que $(P,Q)$ valga en $\mathbf{d}^*(\mathbf{B})$. $\mathrm{tr}_{\mathbf{d}}(P,Q)$ hi afegeix les equacions $(d^\sharp R,d^\sharp R)$ per a cada subterme $R$ de $P$ i de $Q$. Si cada $d(\sigma)$ conté totes les seues variables, aquestes equacions són redundants, i el text ho diu.

## 3. ep-derivors generalitzats (`SGenEpDerivors`)

**Comentari.** Completar una definició d'ep-derivor prenent com a base els
derivors generalitzats.

**Què he fet** (la secció era buida):

- **`DGenEpDerivor`** (nova): un ep-derivor generalitzat entre ep-signatures és un derivor generalitzat $(\varphi,D,d)$ tal que, per a cada $\sigma\in\Sigma_{\mathbf{s},s}$:
  - **(GEP1)**, preservació del domini:
    $d(\sigma)^{\sharp}[D_s]\subseteq\mathrm{Cn}(D_{\mathbf{s}}\cup\mathrm{deft}^{\mathbf{\Lambda}}(d(\sigma)))$;
  - **(GEP2)**, condicions de domini dins dels dominis:
    $\mathrm{Cn}(D_{\mathbf{s}}\cup\mathrm{tr}[\mathrm{def}^{\mathbf{\Sigma}}(\sigma)])=\mathrm{Cn}(D_{\mathbf{s}}\cup\mathrm{deft}^{\mathbf{\Lambda}}(d(\sigma)))$.

  $\mathbf{d}^*(\mathbf{B})$ té com a conjunt subjacent els $B^D_s$, i les operacions són les restriccions de $d(\sigma)^{\mathbf{B}}$.
- **`PGenEpDerivorFunctor`** (nova, amb prova): un ep-derivor generalitzat indueix un functor $\mathsf{PAlg}(\mathbf{\Lambda})\to\mathsf{PAlg}(\mathbf{\Sigma})$.
- **`RGenEpDerivor`** (nova): comprova la coherència amb les seccions anteriors:
  - els ep-derivors són el cas $D=\varnothing$;
  - per a signatures totals, (GEP2) és trivial i (GEP1) equival a la condició de clausura de `RGenDerivorSem`;
  - les dues condicions també són necessàries.

## 4. $\Sigma^{(n)}$ com a ep-signatura (`DSigmaCatCompact`)

**Comentari.** Completar $\Sigma^{(n)}$ com una ep-signatura on l'únic domini
de definició no trivial és
$\mathrm{def}(\circ^k_s)=\{(\mathrm{sc}^k_s(v^s_1),\mathrm{tg}^k_s(v^s_0))\}$.

**Què he fet.**

- A `DSigmaCatCompact` he afegit l'ep-signatura $\mathbf{\Sigma}^{(n)}=(S,\Sigma^{(n)},\mathrm{def}^{\mathbf{\Sigma}^{(n)}})$:
  - les condicions de domini són buides per a les operacions de $\Sigma$, per a $\mathrm{sc}^k_s$ i per a $\mathrm{tg}^k_s$;
  - per a la composició, $\mathrm{def}(\circ^k_s)=\{(\mathrm{sc}^k_s(v^s_0),\mathrm{tg}^k_s(v^s_1))\}$, on $v^s_0\circ^k_s v^s_1$ abreuja $\circ^k_s(v^s_0,v^s_1)$.
- **Observació `RCompactEp`** (nova): les ep-àlgebres de tipus $\mathbf{\Sigma}^{(n)}$ són exactament les $\Sigma^{(n)}$-àlgebres parcials que compleixen (A0), (A$^k$1) i (A$^k$3). Per tant, la QE-varietat de `DVarCompact` és la classe de les $\mathbf{\Sigma}^{(n)}$-àlgebres que compleixen la resta d'axiomes.

⚠️ **He invertit l'ordre de les variables respecte del comentari** (vegeu la decisió A).

## 5. Categoria compacta $\omega$ abans de `DSigmaCatCompact`, i cas $\omega$

**Comentari.** Escriure la definició de categoria compacta $\omega$ abans de
`DSigmaCatCompact`, i modificar `DSigmaCatCompact` perquè considere també el
cas $\omega$.

**Què he fet.**

- He mogut `DCompactOmegaCat` i `DOmegaCatAlg` just després de `DManySortedCatAlg`, amb una frase introductòria. He mogut també l'àlgebra, i no només la categoria, perquè és el seu anàleg natural.
- A `DSigmaCatCompact` ara $n\in\mathbb{N}\cup\{\omega\}$. La nota posterior diu que $\Sigma^{(n)}\subseteq\Sigma^{(m)}$ per a $n\le m\le\omega$ i que $\Sigma^{(\omega)}=\bigcup_n\Sigma^{(n)}$.
- Dins de `RCompactEp` he afegit una nota: **`DVarCompact` no s'estén a $n=\omega$.** La condició «tota cel·la és una $k$-cel·la per a algun $k$» no es preserva per productes, i les QE-varietats sí que són tancades per productes. El text en dona un contraexemple.

## 6. Notació $\circ^{(j,k)}$ a la presentació estesa

**Comentari.** La $j$-composició de $k$-cel·les es denotarà $\circ^{(j,k)}$,
com ja fan `DSigmaCatExtended` i `DVarExtended`.

**Què he fet.** He substituït $\circ^{(j)}$ i $\circ^{(i)}$ a `DOmegaCatExt`, a
les $n$-categories esteses i als $n$-functors estesos. L'índex superior és
sempre la dimensió de les cel·les compostes:

- **(MS3):** $\mathrm{sc}^{(j,k)}(g\circ^{(i,k)}f)=\mathrm{sc}^{(j,k)}(g)\circ^{(i,j)}\mathrm{sc}^{(j,k)}(f)$.
- **(MS8):** $\mathrm{i}^{(k,j)}(g\circ^{(i,j)}f)=\mathrm{i}^{(k,j)}(g)\circ^{(i,k)}\mathrm{i}^{(k,j)}(f)$. He eliminat la frase aclaridora («on the left … on the right …»), perquè la notació ja ho diu.
- **(MS9), (MS2), (MS6), (MS7):** $\circ^{(i,k)}$ i $\circ^{(j,k)}$, segons el cas.
- **Functors:** $F_k(g\circ^{(j,k)}f)=F_k(g)\circ'^{(j,k)}F_k(f)$.
- **Dades:** $\zeta_{j,k}=(\circ^{(j,k)},\mathrm{sc}^{(j,k)},\mathrm{tg}^{(j,k)},\mathrm{i}^{(k,j)})$. A més, «$j$-composition in $C_k$» ara diu «$j$-composition of $k$-cells».

Al document ja no hi queda cap $\circ^{(j)}$ ni cap $\circ^{(i)}$.

## 7. Moure `DOmegaExtCatAlg` i cas $\omega$ de `DSigmaCatExtended`

**Comentari.** Moure aquesta definició abans de `DSigmaCatExtended` i
modificar `DSigmaCatExtended` perquè considere també el cas $\omega$.

**Què he fet.**

- He mogut `DOmegaExtCatAlg` just després de `DExtCatAlg`, és a dir, abans de `DSigmaCatExtended`.
- A `DSigmaCatExtended` ara $n\in\mathbb{N}\cup\{\omega\}$. He introduït la notació $[n]$ per al conjunt de dimensions: $[n]=n+1$ si $n\in\mathbb{N}$, i $[\omega]=\omega$. Cal perquè, per a $\omega$, els sorts són $\omega\times S$ i no $(\omega+1)\times S$. He canviat $n+1$ per $[n]$ dins de la definició.
- La nota posterior diu que $\Sigma^{\mathrm{ext}(\omega)}$ és la unió de les imatges de les inclusions de $\Sigma^{\mathrm{ext}(n)}$, i que per a $n$ finit $[n]=n+1$, que és la notació de les altres definicions.

---

## Decisions que has de revisar

**A. Ordre dels arguments de $\circ^k_s$ (punt 4).** El comentari escrivia
$\mathrm{def}(\circ^k_s)=\{(\mathrm{sc}^k_s(v^s_1),\mathrm{tg}^k_s(v^s_0))\}$.
Amb la convenció del document, $x\circ^k_s y=\circ^k_s(x,y)$, i (A$^k$3) diu
que $x\circ^k_s y$ està definit si i només si
$\mathrm{sc}^k_s(x)=\mathrm{tg}^k_s(y)$. Amb $x=v^s_0$ i $y=v^s_1$, això dona
$(\mathrm{sc}^k_s(v^s_0),\mathrm{tg}^k_s(v^s_1))$, que és el que he escrit. La
versió del comentari correspon a l'ordre diagramàtic. Si la volies així, cal
canviar també (A$^k$3)–(A$^k$6) i (AB$^{l,k}$3). **Recomanació:** mantenir
l'ordre que he posat, que és coherent amb la resta del document.

**B. $\mathrm{tr}_{\mathbf{d}}$ en lloc de $d^\sharp\times d^\sharp$ (punt 2.4).**
És un canvi matemàtic que no demanava el comentari. Sense aquest canvi,
`PEpDerivorFunctor` és falsa per a derivors que «esborren» variables. Una
alternativa és restringir-se a derivors on cada $d(\sigma)$ conté totes les
seues variables i mantenir $d^\sharp\times d^\sharp$. **Recomanació:**
$\mathrm{tr}_{\mathbf{d}}$, que és més general i coincideix amb l'altra opció
en el cas regular.

**C. (GEP1) i (GEP2) són una proposta meua (punt 3).** Les he triat perquè
$\mathbf{d}^*$ siga un functor, i són també necessàries per a això. Si teniu en
ment una altra noció, per exemple sense (GEP1) o amb inclusió, caldrà ajustar
la definició.

**D. Les condicions de domini $D_s$ usen una única variable,** com $\Delta_s(x)$
a [LG18]. Si en algun moment cal que depenguen de més variables, caldria
canviar la definició.

**E. Cas $\omega$ de les especificacions.** No he estés `DVarCompact` a
$\omega$, perquè no és possible (vegeu el punt 5). En canvi, `DVarExtended`
**sí** que es podria estendre a $\omega$: en la presentació estesa no hi ha
condició de finitud, perquè cada cel·la viu en un sort $(k,s)$. No ho he fet
perquè el comentari no ho demanava. Ho proposo com a pas següent.

**F. Notació de variables.** L'Observació `Rdop` numera les variables de
$\downarrow\varphi^\star(\mathbf{s})$ per sorts, com a segments inicials. En
canvi, la secció de les àlgebres de Hall usa $v^{s_j}_j$, per posicions. Per
no prendre partit, he introduït $v^{\mathbf{t}}_j$, «la variable de la lletra
$j$». Caldria unificar les dues convencions algun dia.

**G. El pla de formalització.**
- Els ítems `DSigmaCatCompact` i `DSigmaCatExtended` de `compact.toml` i `extended.toml` estan marcats com a `done`. Ara les definicions inclouen el cas $\omega$, i la compacta també l'estructura d'ep-signatura, que el Lean actual (`compact.signature` i `extended.signature`) no cobreix. El propietari del pla (encosllo) hauria de decidir si cal revisar-los. No he tocat cap fitxer `.toml` ni cap fitxer Lean.
- Els trasllats de definicions no afecten el pla, perquè les referències són etiquetes i no números.
- Les seccions de derivors queden fora de l'abast actual del pla.

## Nous elements del document (etiquetes)

`RGenDerivorSem`, `DEpSignature`, `RSubst`, `DDeft`, `LDeft`, `DCn`,
`DTranslation`, `LTranslation`, `PEpDerivorFunctor`, `REpDerivor`,
`DGenEpDerivor`, `PGenEpDerivorFunctor`, `RGenEpDerivor`, `RCompactEp`.
`DGeneralDerivor` i `DDerivorEP` conserven l'etiqueta, però el contingut és nou.

---
---

# Segona ronda: nous comentaris en roig

Data: 2026-10-13. Hi havia 18 comentaris nous en roig, a més del bloc de
resultats sobre derivors que havies enganxat dins la secció d'ep-derivors
generalitzats. Tots s'han resolt i eliminat. El document compila sense
errors, sense referències indefinides i sense etiquetes duplicades (pdflatex +
bibtex). Ara té 113 pàgines.

Al final hi ha les **decisions que has de revisar**.

## 1. Estructura: comentar les seccions 3, 4 i 5

**Comentari.** Comentar les tres seccions anteriors (*Derivors*,
*Generalized derivors*, *ep-derivors*) i introduir directament els
*generalized ep-derivors*. La secció ha d'incloure les nocions anteriors que
calguen, excepte les àlgebres de Hall, que no s'han de copiar però de les quals
sí es poden fer servir els resultats.

**Què he fet.**
- He comentat les tres seccions línia a línia amb `%`; per recuperar-les, n'hi ha prou de llevar el `%`. Abans he esborrat els seus comentaris en roig, perquè els resol la secció nova.
- He reescrit la secció *Generalized ep-derivors*, que ara és la secció 3 del PDF, amb sis subseccions:
  1. **Notation**: variables, termes i subterme, E-equacions i substitucions. Dels derivors només recorde la definició i tres fets de l'apèndix, (H1)–(H3): $d^\sharp$ és un homomorfisme d'àlgebres de Hall i la composició és la de $\mathsf{Sig}_{\mathfrak d}$. No hi copie res de les àlgebres de Hall. Inclou `RSubst` i un remark nou, `RHomTerm`: els homomorfismes conserven els valors definits.
  2. **ep-signatures**: `DEpSignature`, `DDeft`, `LDeft` i `DCn`.
  3. **Generalized derivors and translations**: `DGeneralDerivor`, `PDeltaFunctor`, `DDerivedPAlg`, `DTranslation` i `LTranslation`.
  4. **Generalized ep-derivors**: `DGenEpDerivor`, `PGenEpDerivorAlg`, `PGenEpDerivorFunctor` i `RGenEpDerivor`.
  5. **La categoria $\mathsf{epSig}_{\mathfrak{gd}}$**: composició, `PEpSiggdCat`, `PGenAlgFun`, `PGenDerClCong` i `DEpAlgCat`.
  6. **Generalized ep-derivors between ep-specifications**: vegeu la decisió C.

## 2. Notació de variables (comentari a l'antiga §4)

**Comentari.** Prendre la notació de variables de la secció de *derived
operations* del document Curry-Howard.

**Què he fet.**
- He adoptat la notació $\downarrow\mathbf{s}$, amb $(\downarrow\mathbf{s})_s=\mathbf{s}^{-1}[\{s\}]$, i l'he identificada amb $V^S_{\mathbf{s}}=\{v^s_i\mid i\in|\mathbf{s}|_s\}$, numerades per sort com al Curry-Howard.
- Aquesta part del Curry-Howard ja és a l'apèndix del `main.tex`, així que hi faig referència (`DLR`, `isovsV`) i no cite el document, que ja no és a `Biblio.bib`.
- $v^{\mathbf{s}}_j$ queda només com a abreviatura de la variable corresponent a la lletra $j$. Així, $v^{\mathbf{s}}_j=v^{s_j}_i$ si aquella lletra és l'aparició $i$-èsima del seu sort.

## 3. Functor $\Delta_{(\varphi,D)}$ (comentari a l'antiga §4)

**Comentari.** Llevar el remark `RGenDerivorSem` i fer una proposició que
definisca $\Delta_{(\varphi,D)}$.

**Què he fet.**
- He eliminat el remark.
- He afegit la nova Proposició `PDeltaFunctor`. Defineix $\Delta_{(\varphi,D)}\colon\mathsf{PAlg}(\Lambda)\to\mathsf{Set}^S$, que envia $\mathbf{B}$ a $B_{(\varphi,D)}$ i $f$ a $f_\varphi|^{B_{(\varphi,D)}}_{A_{(\varphi,D)}}$, exactament com demanaves.
- Les fletxes són els homomorfismes, que conserven les E-equacions; per això el domini és $\mathsf{PAlg}(\Lambda)$.
- També demostre que $\Delta_{(\varphi,\varnothing)}=\Delta_\varphi\circ\mathrm{G}_\Lambda$.

## 4. Notació $\mathsf{epAlg}$

**Comentari.** $\mathsf{epAlg}(S,\Sigma,\mathrm{def}^{\mathbf\Sigma})$ ha de
ser la subcategoria plena de $\mathsf{PAlg}(S,\Sigma)$ de les ep-àlgebres, i
cal canviar la notació a tot el document.

**Què he fet.**
- L'he introduïda a `DEpSignature` i l'he usada a tot arreu on la categoria era d'ep-àlgebres.
- $\mathsf{PAlg}(\boldsymbol{\mathcal C}^{\dots})$ es manté per a les QE-varietats.
- Per a les categories compacta i estesa demostre la igualtat $\mathsf{PAlg}(\boldsymbol{\mathcal{C}}^{\mathbf{\Sigma}^{(n)}})=\mathsf{epAlg}(\mathbf{\Sigma}^{(n)},\mathcal{C}^{\mathbf{\Sigma}^{(n)}})$ (`RCompactEp`, `PExtendedIdent`), i el mateix per a l'estesa.

## 5. `RSubst`

**Comentari.** Llevar-lo si no s'usa a la resta del document.

**Què he fet.** Es fa servir a `LDeft`, `LTranslation`, `PDeltaFunctor` i
`PGenEpDerivorAlg`. Per tant, l'he mantingut, dins la subsecció de notació.

## 6. Equació de $\mathrm{Cn}$ més neta

**Què he fet.** He introduït la classe de models
$\mathrm{Mod}^{\mathbf\Sigma}_X(\mathcal E)$, de manera que la definició queda
$\mathrm{Cn}^{\mathbf\Sigma}_X(\mathcal E)=\{e\mid\mathrm{Mod}(\mathcal E)\subseteq\mathrm{Mod}(\{e\})\}$.

## 7. Termes i subterme del Curry-Howard

**Què he fet.**
- Uso $\mathrm{Subt}_\Sigma(P)$, el conjunt $S$-sortit de subterme, en lloc del meu $\mathrm{Sb}(P)$.
- També faig servir la seua caracterització recursiva.
- Totes dues són a l'apèndix; hi he afegit les etiquetes `DSubt` i `RSubt` perquè es puguen citar.

## 8. Els resultats sobre derivors, adaptats

**Comentari.** Adaptar `PFunSig`, `PDerClCong`, `PAlgFun`, el diagrama i
`DAlgCat` als *generalized ep-derivors*, mantenint-ne l'estil.

**Què he fet.**

| Original | Nova versió |
|---|---|
| `PFunSig` | `PGenEpDerivorFunctor`: $\mathrm{Alg}_{\mathfrak{gd}}(\mathbf d)=\mathbf d^\ast_{\mathfrak{gd}}$ |
| el diagrama | dins `PGenEpDerivorFunctor`: $\mathrm G_{\mathbf\Sigma}\circ\mathbf d^\ast_{\mathfrak{gd}}=\Delta_{(\varphi,D)}\circ\mathrm{In}$ |
| `PDerClCong` | `PGenDerClCong` |
| `PAlgFun` | `PGenAlgFun` |
| `DAlgCat` | `DEpAlgCat` ($\mathsf{epAlg}_{\mathfrak{gd}}$) |

- Les etiquetes són noves perquè les originals ja existien a l'apèndix; el bloc enganxat les duplicava.
- A `PGenDerClCong` no he pogut usar l'argument de l'original (el functor aplicat a la inclusió o a la projecció): el quocient d'una ep-àlgebra no és necessàriament una ep-àlgebra. Per això la prova és directa, per inducció sobre termes.

## 9. $\mathsf{epSig}_{\mathfrak{gd}}$, $\mathbf d^\ast_{\mathfrak{gd}}$ i el paràgraf convertit en proposició

**Què he fet.**
- El paràgraf que definia $\mathbf d^\ast(\mathbf B)$ és ara la Proposició `PGenEpDerivorAlg`, escrita amb $\Delta_{(\varphi,D)}$. És una equivalència: (GEP1)+(GEP2) es compleixen si i només si cada $\mathbf\Lambda$-àlgebra és tancada i $\mathbf d^\ast(\mathbf B)$ és una $\mathbf\Sigma$-àlgebra.
- `PGenEpDerivorFunctor` usa la notació $\mathbf d^\ast_{\mathfrak{gd}}$.
- La categoria és la Proposició `PEpSiggdCat`. **L'ordre és diferent del que demanaves**: vegeu la decisió B.

## 10. Graduació i unificació

**Què he fet.**
- **Graduació.** He definit el derivor $\mathbf g^{(n)}$ (`DGradDerivor`) a partir de la teua idea, amb dues correccions:
  - per a $n$ finit, $D_{(n,s)}=\varnothing$, perquè $\mathrm{sc}^n$ no existeix a $\Sigma^{(n)}$;
  - la identitat és $\mathrm i^{(k,j)}\mapsto v_0$, amb la notació $\mathrm i^{(k,j)}$ del document.
- `PGradDerivor` demostra (GEP1)–(GEP3): el functor transforma àlgebres compactes en esteses. La prova tradueix cada axioma (EA) a un axioma (A)/(AB).
- `DGraduation` defineix $\mathrm{Gd}^{(n)}_{\mathbf\Sigma}$ i la seua birestricció, també per a $n=\omega$.
- **Unificació.** He definit $\mathbf u^{(n)}$ (`DUnifDerivor`) a partir de la teua idea, amb $\#^k\mapsto\circ^{(k,n)}$. `PUnifDerivor` en demostra les propietats i `DUnification` defineix $\mathrm{Uf}^{(n)}$.
- **Unificació, cas $\omega$.** No pot venir d'un *generalized derivor* (vegeu la decisió E). L'he definida com un colímit dels casos finits (`DUnificationOmega`, `PUnificationOmega`).
- **Relació entre tots dos.**
  - `PUnifGrad`: $\mathrm{Uf}\circ\mathrm{Gd}=\mathrm{Id}$. Ho demostre veient que el derivor compost $\mathbf g\circ\mathbf u$ és equivalent a la identitat. Per a $\omega$, només és un isomorfisme natural.
  - `PGradUnif`: $\mathrm{Gd}\circ\mathrm{Uf}\cong\mathrm{Id}$, calculant el compost $\mathbf u\circ\mathbf g$.
  - Corol·lari nou `CGdUfEquiv`: totes dues són equivalències de categories.
- **Identificacions prèvies.** Per definir el functor sobre $\mathsf{nCatAlg}$, he afegit `PCompactIdent`, que demostra $\mathsf{nCatAlg}(\mathbf\Sigma)=\mathsf{PAlg}(\boldsymbol{\mathcal{C}}^{\mathbf{\Sigma}^{(n)}})$ i diu que, per a $\omega$, és una subcategoria plena pròpia. He afegit també `PExtendedIdent` per al cas estés.

## 11. Discretització i truncació

**Què he fet.**
- He reescrit la secció sencera; del text antic sobre la truncació no queda res.
- Per a $m\le n$, amb $n\in\mathbb N\cup\{\omega\}$, he definit els derivors de discretització, $\boldsymbol\delta^{(n,m)}$ i $\boldsymbol\delta^{\mathrm{ext}(n,m)}$, i de truncació, $\boldsymbol\tau^{(m,n)}$ i $\boldsymbol\tau^{\mathrm{ext}(m,n)}$. Demostre que són *generalized ep-derivors* (`PDiscDerivor`, `PDiscExtDerivor`, `PTruncExtDerivor`) i en definisc els functors $\mathrm D^{(n,m)}_{\mathbf\Sigma}$ i $T^{(m,n)}_{\mathbf\Sigma}$, en les versions compacta i estesa.
- **Relacions** (`PTruncDisc`, `PDiscTruncAdj`, `PTruncComp`):
  - $T\circ\mathrm D=\mathrm{Id}$, demostrat amb derivors compostos;
  - $\mathrm D\dashv T$, amb unitat identitat; la counitat és la inclusió de les $m$-cel·les en la versió compacta i $\mathrm i^{(k,m)}$ en l'estesa;
  - $T^{(m,n)}\circ T^{(n,p)}=T^{(m,p)}$, que és el fet que usen les seccions de límits. Ara el remark `RTmnCatAlgProjSys` hi remet.
- He conservat les etiquetes `DTmnCatAlg` i `DTmnExtCatAlg`, que són al pla. El functor és el mateix que abans: les $m$-cel·les són exactament les cel·les que són $k$-cel·les per a tot $k\ge m$, per (AB$^{m,k}$1).

## 12. Notació $[n]$

**Comentari.** No introduir $[n]$; usar $n+1$.

**Què he fet.**
- He reescrit `DSigmaCatExtended` per a $n\in\mathbb N$ amb $n+1$. Per a $\omega$ hi ha una frase final: «les mateixes clàusules amb $\omega$ en lloc de $n+1$».
- `DVarExtended` es completa de la mateixa manera per a $\omega$.
- `DVarCompact` admet ara $n\in\mathbb N\cup\{\omega\}$.

---

## Decisions que has de revisar (segona ronda)

**A. Condicions de domini per a cada operació, $D_\sigma$ (la decisió més important).**
- **Canvi.** Ara un *generalized derivor* $(\varphi,D,d)$ té $D=((D_s)_s,(D_\sigma)_\sigma)$: a més del domini de cada sort, hi ha un conjunt d'E-equacions que restringeix el domini de cada símbol.
- **Raó 1: discretització.** Sense $D_\sigma$, la discretització no pot venir de cap derivor. Cal que $x\circ^m y$ estiga definit si i només si $x=y$, i cap terme no ho expressa: en un monoide, vist com a categoria compacta, tot terme és total.
- **Raó 2: composició.** Sense $D_\sigma$, la composició de dos *generalized ep-derivors* no és en general un *generalized ep-derivor*. Si $\mathbf e$ oblida una variable, $(\mathbf e\circ\mathbf d)^\ast$ pot estar definit on $\mathbf d^\ast\circ\mathbf e^\ast$ no ho està.
- **Compatibilitat.** És la contrapartida de la fórmula $\Phi^\sigma$ de [LG18]. Amb $D_\sigma=\varnothing$ es recupera tot el que teníem: les teues idees per a $\mathrm{Gd}$ i $\mathrm{Uf}$ no en necessiten.

**B. Ordre de les proposicions.**
- **Què demanaves.** Primer la categoria $\mathsf{epSig}_{\mathfrak{gd}}$, després la proposició del paràgraf i després `PGenEpDerivorFunctor`.
- **Per què no ho he pogut fer.** La prova que el compost de dos *generalized ep-derivors* ho torna a ser necessita saber que $\mathbf e^\ast(\mathbf C)$ és una ep-àlgebra, que és justament la proposició del paràgraf.
- **Ordre que he fet servir.** `PGenEpDerivorAlg` → `PGenEpDerivorFunctor` → `PEpSiggdCat`. Ho explique en una frase al començament de la subsecció.

**C. Morfismes de $\mathsf{epSig}_{\mathfrak{gd}}$ com a classes d'equivalència.**
- **Problema.** La composició sintàctica (Definició `DGenEpComp`) no és associativa literalment, i la identitat no hi és neutra. Els conjunts d'equacions que resulten són diferents, encara que tinguen els mateixos models.
- **Solució.** Els morfismes són classes. Dos *generalized ep-derivors* són equivalents si tenen la mateixa $\varphi$ i el mateix functor.
- **Alternativa (no recomanada).** Normalitzar els conjunts $D$ a la seua clausura per $\mathrm{Cn}$; seria més feixuc d'escriure.

**D. Relativització a especificacions: ep-specifications i (GEP3).**
- **Problema.** El derivor de graduació no compleix (GEP1) sobre totes les $\mathbf\Sigma^{(n)}$-àlgebres: en una àlgebra on $\mathrm{sc}^j$ no és idempotent, la $j$-font d'una cel·la no és una $j$-cel·la. Per tant, «el functor entre ep-àlgebres» que demanaves no està definit sobre totes les ep-àlgebres, sinó només sobre els models de $\boldsymbol{\mathcal C}^{\mathbf\Sigma^{(n)}}$.
- **Solució.** He afegit la subsecció `SEpSpec`:
  - ep-especificacions $(\mathbf\Sigma,\mathcal E)$;
  - $\mathrm{Cn}^{\mathbf\Lambda,\mathcal F}$;
  - la condició (GEP3): $\mathbf d^\ast$ envia models a models;
  - un criteri sintàctic (`LTranslationQE`);
  - la Proposició `PGenEpSpec`, que estén tots els resultats a $\mathsf{epSpec}_{\mathfrak{gd}}$.
- **Relació amb el que demanaves.** $\mathsf{epSig}_{\mathfrak{gd}}$ és la subcategoria plena de les especificacions amb $\mathcal E=\varnothing$. La «birestricció» que demanaves és exactament (GEP3).

**E. La unificació $\omega$ no ve d'un derivor.**
- **Problema.** Un *generalized derivor* envia cada sort a un únic sort $(k,s)$, i per tant només veu cel·les d'una dimensió. L'argument és al text: una ω-categoria estesa amb una sola cel·la fins a la dimensió $k$.
- **Solució.** He definit $\mathrm{Uf}^{(\omega)}$ com el colímit de les àlgebres $\mathrm D^{(\omega,p)}\mathrm{Uf}^{(p)}T^{\mathrm{ext}(p,\omega)}(\mathbf A)$.
- **Conseqüència.** Per a $\omega$, els resultats de relació són isomorfismes naturals, no igualtats.

**F. Notació dels functors.**
- $T^{(m,n)}$ va en cursiva, com a les seccions de límits.
- La discretització és $\mathrm D^{(n,m)}$, com al Projecte-Investigador ($D^{(n+1,n)}_\Sigma$).
- La truncació tenia dues notacions: $U^{(n,n+1)}$ al Projecte-Investigador i $T^{(m,n)}$ al `main.tex`. He mantingut la del `main.tex`.

**G. Pla de formalització.**
- No he tocat cap `.toml` ni cap fitxer Lean.
- L'ítem `SDiscretization` de `truncation.toml` està «blocked» perquè la subsecció només tenia títol. Ara té contingut; el propietari del pla (encosllo) podria desbloquejar-lo.
- L'ítem `DTmnCatAlg, DTmnExtCatAlg` («done») defineix el mateix functor que abans, però ara també per a $n=\omega$ i a partir d'un derivor. Convé revisar-lo.
- Els ítems exclosos `SDerivors`, `SGenDerivors` i `SEpDerivors` apunten ara a seccions comentades.
- No he pogut executar `stemma check`, perquè Lean no està instal·lat en aquest entorn.

## Nous elements (segona ronda)

`SGenEpNotation`, `RHomTerm`, `SEpSignatures`, `SGenDerivorsTr`,
`PDeltaFunctor`, `DDerivedPAlg`, `RTrRegular`, `SGenEpDerivorsDef`,
`PGenEpDerivorAlg`, `SEpSiggd`, `DGenEpComp`, `LGenEpComp`, `PEpSiggdCat`,
`PGenAlgFun`, `PGenDerClCong`, `DEpAlgCat`, `SEpSpec`, `DEpSpec`,
`DGenEpDerivorSpec`, `LTranslationQE`, `PGenEpSpec`, `PCompactIdent`,
`PExtendedIdent`, `SGraduationSub`, `DGradDerivor`, `PGradDerivor`,
`DGraduation`, `SUnificationSub`, `DUnifDerivor`, `PUnifDerivor`,
`DUnification`, `DUnificationOmega`, `PUnificationOmega`, `SGradUnif`,
`CGdUfEquiv`, `DDiscDerivor`, `PDiscDerivor`, `DDiscretization`,
`DDiscExtDerivor`, `PDiscExtDerivor`, `DDiscretizationExt`, `DTruncDerivor`,
`PTruncExtDerivor`, `SDiscTrunc`, `PTruncDisc`, `PDiscTruncAdj`,
`PTruncComp`; i, a l'apèndix, `DLR`, `DSubt`, `RSubt`. Desapareixen `RGenDerivorSem` i les etiquetes que només eren a les seccions
comentades (`DDerivor`, `PSigdCat`, `DDerivorEP`, `PEpDerivorFunctor`,
`REpDerivor`, …). `DEpSignature`, `RSubst`, `DDeft`, `LDeft`, `DCn`,
`DTranslation`, `LTranslation`, `DGeneralDerivor`, `DGenEpDerivor`,
`PGenEpDerivorFunctor` i `RGenEpDerivor` es reutilitzen a la secció nova.

---
---

# Tercera ronda: respostes a les decisions A–E

Data: 2026-10-13. El document compila sense errors, sense referències
indefinides i sense etiquetes duplicades; ara té 118 pàgines.

## B. Notació $\mathbf d^\ast_{\mathfrak{gd}}(\mathbf B)$

Totes les àlgebres transformades s'escriuen ara amb el subíndex:
$\mathbf d^\ast_{\mathfrak{gd}}(\mathbf B)$,
$(\mathbf e\circ\mathbf d)^\ast_{\mathfrak{gd}}(\mathbf C)$,
$(\boldsymbol\delta^{(n,m)})^\ast_{\mathfrak{gd}}(\mathbf B)$, etc.
He fet 23 substitucions, totes a les seccions actives.

## E. Reestructuració del cas $\omega$

- **Seccions finites.** Les seccions de graduació/unificació
  (`SGraduation`) i de discretització/truncació (`STruncation`) ara només
  tracten casos finits ($n\in\mathbb N$, $m\le n$). Hi he afegit:
  - `PGdUfAdj`: $\mathrm{Gd}^{(n)}\dashv\mathrm{Uf}^{(n)}$, amb unitat la
    identitat i counitat $\theta^{-1}$. És una equivalència adjunta.
  - A `PTruncComp`, la igualtat $T^{(n,p)}\circ\mathrm D^{(p,m)}=\mathrm D^{(n,m)}$.
  - Nova subsecció `SCompatGdUf`, amb `PCompatGdUf`:
    1. $T^{\mathrm{ext}}\circ\mathrm{Gd}=\mathrm{Gd}\circ T$;
    2. $\mathrm{Gd}\circ\mathrm D=\mathrm D^{\mathrm{ext}}\circ\mathrm{Gd}$;
    3. $\mathrm{Uf}\circ\mathrm D^{\mathrm{ext}}=\mathrm D\circ\mathrm{Uf}$;
    4. $\mathrm{Uf}^{(m)}\circ T^{\mathrm{ext}(m,n)}\cong T^{(m,n)}\circ\mathrm{Uf}^{(n)}$,
       amb l'isomorfisme $\beta^{(m,n)}$ donat per les identitats $\mathrm i^{(n,m)}$.
- **`SLimitCompact`.**
  - Defineix les projeccions $T^{(n,\omega)}$ (`DTnOmegaCatAlg`).
  - Ara té la demostració de `PUnivPropCatAlg`, que no en tenia: el límit
    d'una família compatible és la unió de les cel·les, i cada operació es
    calcula en un nivell finit.
  - Afegeix el corol·lari `CLimitNat`: morfismes i transformacions naturals
    cap a $\omega\mathsf{CatAlg}$ es determinen nivell a nivell.
- **`SLimitExtended`.** Defineix $T^{\mathrm{ext}(n,\omega)}$
  (`DTnOmegaExtCatAlg`) i afegeix `CLimitNatExt`.
- **Nova secció `SOmegaFunctors`.** Els quatre functors $\omega$ es defineixen
  per la propietat universal:
  - **Truncació.** $T^{(m,\omega)}$ i $T^{\mathrm{ext}(m,\omega)}$ són les
    projeccions del límit.
  - **Graduació.** $\mathrm{Gd}^{(\omega)}$ es defineix per la família
    $\mathrm{Gd}^{(n)}\circ T^{(n,\omega)}$ (`DGdOmega`).
  - **Unificació.** La família $\mathrm{Uf}^{(n)}\circ T^{\mathrm{ext}(n,\omega)}$
    només és compatible llevat d'isomorfisme ($\beta$), i la propietat
    universal demana igualtats. Per això he introduït la *unificació
    normalitzada* $\widetilde{\mathrm{Uf}}^{(n)}$ (`LNormalForm`, `DNormUnif`,
    `LNormUnif`): cada cel·la es representa per la seua forma normal,
    $(k,y)$ amb $y$ una $k$-cel·la no degenerada. Aquesta família sí que és
    compatible estrictament, i defineix $\mathrm{Uf}^{(\omega)}$ (`DUfOmega`).
    També explique per què no pot venir d'un derivor (el contraexemple del
    monoide $\{e,f\}$).
  - **Discretització.** $\mathrm D^{(\omega,m)}$ i $\mathrm D^{\mathrm{ext}(\omega,m)}$
    es defineixen per les famílies $F_n$ (discretització si $n\ge m$,
    truncació si $n\le m$) (`DDiscOmega`).
  - **Relacions.**
    - `POmegaGdUf`: $\mathrm{Uf}^{(\omega)}\mathrm{Gd}^{(\omega)}\cong\mathrm{Id}$ i
      $\mathrm{Gd}^{(\omega)}\mathrm{Uf}^{(\omega)}\cong\mathrm{Id}$; hi ha una
      equivalència adjunta.
    - `POmegaDiscTrunc`: $T\circ\mathrm D=\mathrm{Id}$ i $\mathrm D\dashv T$, en
      les versions compacta i estesa.
- **Quadrat algebraic (`SAlgSquare`).**
  - **Nivell $(n,m)$** (`PAlgSquareFinite`, amb diagrama):
    - $\mathsf C=\mathsf{mCatAlg}$, $\mathsf D=\mathsf{mCat^{ext}Alg}$,
      $\mathsf C'=\mathsf{nCatAlg}$, $\mathsf D'=\mathsf{nCat^{ext}Alg}$;
    - horitzontals $\mathrm{Gd}\dashv\mathrm{Uf}$; verticals $\mathrm D\dashv T$;
    - $\alpha=\mathrm{id}$ (igualtat estricta) i $\beta=\beta^{(m,n)}$.
  - **Nivell $(\omega,m)$** (`PAlgSquareOmega`):
    - el mateix amb $\mathsf C'=\omega\mathsf{CatAlg}$ i $\mathsf D'=\omega\mathsf{Cat^{ext}Alg}$;
    - $\alpha=\mathrm{id}$, per la unicitat de la propietat universal;
    - $\beta=\nu^{-1}$: cada $m$-cel·la va a la seua forma normal.
- **Correcció a `DefAlgSquare`.** El text deia «adjunction from
  $\mathsf D$ to $\mathsf C$», etc. Amb la convenció de `DAdj`, això fa que
  $F\colon\mathsf D\to\mathsf C$, i aleshores $F'\circ J$ i $H\circ F$ no
  tipen. El diagrama, en canvi, posa $F\colon\mathsf C\to\mathsf D$, que sí
  que tipa. He reescrit els quatre ítems indicant explícitament els tipus i
  quin és l'adjunt esquerre, d'acord amb el diagrama. El document
  Curry-Howard (Definició 2.1.8) té la mateixa ambigüitat.

## A, C i D

Les he resolt en la ronda següent; vegeu més avall.

---
---

# Quarta ronda: nou disseny dels *generalized ep-derivors* (A, C, D)

Data: 2026-10-13. Has acceptat A i C. Per a D has triat definir el functor
sobre totes les àlgebres parcials i comprovar després que envia models a
models. He reescrit la secció *Generalized ep-derivors* i les proves que en
depenen. El document compila sense errors i sense referències indefinides ni
etiquetes duplicades.

## A. Sense $D_\sigma$

- **Generalized derivor.** Torna a ser $(\varphi,D,d)$, amb un domini per
  a cada sort (`DGeneralDerivor`).
- **El domini d'una operació no és una dada.** Es defineix per recursió:
  - $\mathrm{Dom}_{\mathbf d}(\sigma)$ =
    $D_{\mathbf s}\cup\mathrm{tr}_{\mathbf d}[\mathrm{def}(\sigma)]\cup\{(d\sigma,d\sigma)\}\cup d(\sigma)^\sharp[D_s]$;
  - és a dir: els arguments són als dominis, les condicions de domini de
    $\sigma$ traduïdes es compleixen, $d(\sigma)$ està definit i el seu
    valor cau dins del domini (`DDomTr`);
  - la traducció $\mathrm{tr}_{\mathbf d}$ i les condicions de definició
    $\mathrm{dfd}_{\mathbf d}$ dels subterme es defineixen alhora.
- **Hipòtesi nova.** Perquè la recursió estiga ben fundada, les
  ep-signatures han de complir que la relació «$\tau$ apareix a
  $\mathrm{def}(\sigma)$» siga ben fundada. Ho he afegit a `DEpSignature`, i
  ho he comprovat per a $\mathbf\Sigma^{(n)}$ i $\mathbf\Sigma^{\mathrm{ext}(n)}$.
- **Discretització.** Ja no necessita cap dada extra: la condició de domini
  de $\circ^k$ es tradueix a $v_0=v_1$.

## C. Categoria estricta, sense quocients

- **Dominis tancats.** Els dominis $D_s$ d'un *generalized ep-derivor* han
  de ser tancats per $\mathrm{Cn}$ respecte de l'especificació de destinació.
  Als exemples, els escrivim pels generadors.
- **Composició.** El domini compost és
  $\mathrm{Cn}(E\cup\mathrm{tr}_{\mathbf e}[D_s])$.
- **Resultat.** $\mathsf{epSpec}_{\mathfrak{gd}}$ és una categoria estricta
  (`PEpSiggdCat`), i $\mathsf{epSig}_{\mathfrak{gd}}$ n'és la subcategoria
  plena de les ep-signatures.
- **Conseqüència.** Les igualtats entre derivors compostos són ara igualtats
  de veritat, no equivalències: $\mathbf g\circ\mathbf u=\mathrm{id}$,
  $\boldsymbol\delta\circ\boldsymbol\tau=\mathrm{id}$, i les composicions
  de truncacions i de discretitzacions.

## D. Functor sobre totes les àlgebres parcials

- **Functor.** Per a qualsevol *generalized derivor*,
  $\mathbf d^\ast_{\mathfrak{gd}}$ és un functor
  $\mathsf{PAlg}(\Lambda)\to\mathsf{PAlg}(\Sigma)$, sense cap condició
  (`DDerivedPAlg`, `PGenEpDerivorFunctor`).
- **Definició.** Un *generalized ep-derivor* entre ep-especificacions és un
  *generalized derivor*, amb els dominis tancats, que envia models a models
  (`DGenEpDerivor`).
- **Criteri sintàctic** (`PGenEpDerivorAlg`):
  - (GEP1): les condicions de domini traduïdes impliquen que $d(\sigma)$
    està definit i cau dins del domini;
  - (GEP2): es compleixen els axiomes.
- **Composició.** Només funciona sobre els models (`LGenEpComp`), com havies
  acceptat. Al text hi ha un comentari que ho explica.
- **Les sis construccions** ($\mathrm{Gd}$, $\mathrm{Uf}$, $\mathrm D$,
  $T$, compactes i esteses) es defineixen ara sobre totes les àlgebres
  parcials. Les proposicions corresponents en comproven les dues condicions
  i en prenen la birestricció a les àlgebres categorials.

## Altres canvis

- **Eliminats.** `DDeft` i `LDeft` (la $\mathrm{deft}$ de Reichel), que ja
  no es feien servir; també la subsecció `SEpSpec` i els resultats
  `PGenEpSpec`, `LTranslationQE` i `RTrRegular`, que ara són innecessaris.
- **Nous.** `DDomTr`, `PDomainDef` (el domini de $\sigma$ en
  $\mathbf d^\ast_{\mathfrak{gd}}(\mathbf B)$ és on es compleixen les seues
  condicions de domini i $d(\sigma)$ està definit i cau dins del domini), i
  un comentari després de `LGenEpComp`: dos *generalized ep-derivors* amb les
  mateixes $\varphi$ i $d$ són iguals si tenen els mateixos dominis als models.
- **Diferència amb Reichel.** El `RGenEpDerivor` ara la indica: Reichel exigeix
  que les condicions traduïdes siguen *equivalents* a la definició de
  $d(\sigma)$; ací només es demana una implicació, perquè el domini de
  $\sigma$ queda retallat per les condicions de domini.
