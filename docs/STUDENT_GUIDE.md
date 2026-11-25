# Understanding the Nyquist Stability Criterion Proof (Student Walkthrough)

*(Written for Bachelor / FH / undergraduate Electrical Engineering, Mechatronics, and Computer Science students who have seen basic control loops and calculus, and want to understand what is actually happening inside the proof.)*

> **Honest Disclaimer:** I (the repository owner) have some basic background in control theory, **but I am not a Lean 4 or formal-mathematics expert—what is going on in these proofs is genuinely above my level.** Virtually all the Lean code, proofs, and this explanation were written by AI from my prompts. Every theorem, however, has been mechanically checked line by line by the Lean 4 kernel with zero `sorry`s and only Lean's three standard axioms.

---

## 1. The Big Picture: Why Do We Even Need Nyquist?

Suppose you have a plant $G(s)$ and a controller $C(s)$ connected in a standard **unity negative feedback** loop:

```text
   r(s) ──►( + )──►[ L(s) = C(s)G(s) ]──┬──► y(s)
             ▲ -                         │
             └───────────────────────────┘
```

Here $L(s) = \frac{N(s)}{D(s)}$ is the **open-loop transfer function**. Doing the algebra around the loop gives the **closed-loop transfer function**:

$$T(s) = \frac{L(s)}{1 + L(s)} = \frac{N(s)}{D(s) + N(s)}.$$

### What does "stable" mean in the $s$-plane?
A linear system's natural time response is a sum of terms like $e^{s_k t}$, where the $s_k$ are the **poles** of $T(s)$—that is, the roots of the closed-loop characteristic polynomial:

$$D(s) + N(s) = 0 \qquad (\text{equivalently, } 1 + L(s) = 0).$$

* If $\operatorname{Re}(s_k) < 0$ (strictly in the **Left Half-Plane, LHP**), then $|e^{s_k t}| = e^{\operatorname{Re}(s_k) t} \to 0$ as $t \to \infty$: vibrations die out. Such a polynomial is called **Hurwitz stable** (`IsHurwitz`).
* If $\operatorname{Re}(s_k) > 0$ (in the **Right Half-Plane, RHP**), then $|e^{s_k t}|$ blows up exponentially!

### Why not just solve $D(s) + N(s) = 0$ directly?
1. For high-degree polynomials, finding roots numerically doesn't give you design intuition (how much gain can I add before it oscillates?).
2. Even worse: if your system has a **time delay** $\tau > 0$ (like a conveyor belt, a thermal pipe, or network latency), the open-loop transfer function picks up a factor $e^{-\tau s}$:
   $$L_\tau(s) = \frac{N(s)}{D(s)} e^{-\tau s}.$$
   Then $D(s) + N(s)e^{-\tau s} = 0$ is **not a polynomial anymore**—it has infinitely many roots, so algebraic tests like Routh–Hurwitz completely break down.

**Harry Nyquist's brilliant idea (1932):**
You don't need to find the roots inside the entire right half-plane. Just walk along the **imaginary axis** $s = i\omega$ (steady-state sine-wave frequencies from $\omega = -\infty$ to $+\infty$), plot $L(i\omega)$ in the complex plane, and count **how many times the curve wraps around the critical point $-1$**!

The **Nyquist formula** says:

$$N_{\text{CCW}} = P - Z \qquad \text{(or clockwise: } N_{\text{CW}} = Z - P\text{)}$$

where:
* **$P$** (`rhpRootCount D`) = number of **open-loop** unstable poles (roots of $D$ with $\operatorname{Re}(s) > 0$),
* **$Z$** (`rhpRootCount (D + N)`) = number of **closed-loop** unstable poles (roots of $D+N$ with $\operatorname{Re}(s) > 0$),
* **$N_{\text{CCW}}$** = net **counterclockwise** encirclements of $-1$ by $L(i\omega)$ (or equivalently, encirclements of $0$ by the **return difference** $F(s) := 1 + L(s)$).

For closed-loop stability ($Z = 0$), you simply check $N_{\text{CCW}} = P$ (and if your open-loop plant is already stable, $P = 0$, so the curve must encircle $-1$ **zero times**).

---

## 2. How Do You Turn "Encirclements" into Rigorous Math?

Drawing loops with a pen is intuitive, but a formal theorem prover like Lean needs an exact mathematical definition of "how many times a curve wraps around $0$". Our proof actually gives **two** completely equivalent ways—and proves they give the exact same answer!

### Way 1: The Logarithmic-Derivative Integral (`nyquistEncirclementsCCW`)
Suppose a smooth curve $F(i\omega) \in \mathbb{C} \setminus \{0\}$ can be written in polar form with a continuous angle $\Phi(\omega)$:

$$F(i\omega) = r(\omega) e^{i \Phi(\omega)}, \qquad r(\omega) = |F(i\omega)| > 0.$$

Differentiate with respect to $\omega$ using the product rule and divide by $F(i\omega)$:

$$\frac{\frac{d}{d\omega} F(i\omega)}{F(i\omega)} = \frac{r'(\omega) e^{i\Phi(\omega)} + r(\omega) \cdot i\Phi'(\omega) e^{i\Phi(\omega)}}{r(\omega) e^{i\Phi(\omega)}} = \frac{r'(\omega)}{r(\omega)} + i\,\Phi'(\omega) = \frac{d}{d\omega}\ln r(\omega) + i\,\Phi'(\omega).$$

Now integrate from $\omega = -R$ to $\omega = +R$:

$$\int_{-R}^{R} \frac{\frac{d}{d\omega} F(i\omega)}{F(i\omega)}\,d\omega = \underbrace{\big(\ln r(R) - \ln r(-R)\big)}_{\text{radius ratio } \to 0 \text{ as } R \to \infty} + i\,\underbrace{\big(\Phi(R) - \Phi(-R)\big)}_{\text{net angle swept!}}.$$

If $F(s) = 1 + L(s)$ approaches a nonzero constant as $|\omega| \to \infty$ (for strictly proper systems $1 + L(i\omega) \to 1$), then $\ln r(R) - \ln r(-R) \to 0$. Dividing by $2\pi i$ leaves:

$$N_{\text{CCW}} = \frac{1}{2\pi i} \int_{-\infty}^{+\infty} \frac{\frac{d}{d\omega}(1 + L(i\omega))}{1 + L(i\omega)}\,d\omega = \frac{\Phi(+\infty) - \Phi(-\infty)}{2\pi}.$$

**Aha moment:** Each full counterclockwise loop adds $+2\pi$ to $\Phi$, so dividing by $2\pi i$ literally counts the net winding number!

### Way 2: Continuous Phase Unwrapping (`Nyquist/PhaseLift.lean`)
If you've ever called `unwrap(angle(H))` in MATLAB or Python, you already know Way 2: instead of integrating, you explicitly construct a **continuous** real angle function $\Phi : \mathbb{R} \to \mathbb{R}$ without $2\pi$ jumps such that $1 + L(i\omega) = |1 + L(i\omega)| e^{i \Phi(\omega)}$. Then `nyquist_phase_lift` proves $\Phi(+\infty) - \Phi(-\infty) = 2\pi(P - Z)$, and `continuous_phase_lift_unique` proves via the Intermediate Value Theorem that **any** two continuous phase unwrappings can only differ by a single constant integer multiple $2\pi k$, so the net phase change is completely independent of how you unwrapped it!

---

## 3. Walking Through the Rational Proof Step by Step

Let's follow the exact chain of ideas in `LogDeriv.lean` → `ImagAxisIntegral.lean` → `SemicircleIntegral.lean` → `Criterion.lean`.

### Step A: Split $1 + L(s)$ into Simple Poles and Zeros (`LogDeriv.lean`)
Because $\mathbb{C}$ is algebraically closed (Fundamental Theorem of Algebra), any nonzero polynomials $D(s)$ and $D(s) + N(s)$ factor completely into linear pieces:

$$D(s) + N(s) = c_1 \prod_{j} (s - z_j), \qquad D(s) = c_2 \prod_{k} (s - p_k).$$

Therefore:

$$F(s) = 1 + \frac{N(s)}{D(s)} = \frac{D(s) + N(s)}{D(s)} = \frac{c_1}{c_2} \cdot \frac{\prod_j (s - z_j)}{\prod_k (s - p_k)}.$$

Taking the logarithmic derivative $F'(s)/F(s)$ turns **products into sums** and **quotients into differences**:

$$\frac{F'(s)}{F(s)} = \sum_j \frac{1}{s - z_j} - \sum_k \frac{1}{s - p_k}.$$

Along the imaginary axis $s = i\omega$, the chain rule gives an extra factor of $i$:

$$\text{nyquistIntegrand}(\omega) = \sum_j \frac{i}{i\omega - z_j} - \sum_k \frac{i}{i\omega - p_k}.$$

This is huge! Instead of wrestling with a complicated rational function of degree 50, we only have to understand **one single linear factor** $\frac{i}{i\omega - a}$ at a time!

---

### Step B: What Does One Single Factor $\frac{i}{i\omega - a}$ Do Along $i\mathbb{R}$? (`ImagAxisIntegral.lean` & `PhaseLift.lean`)

Let $a = \alpha + i\beta$ with $\alpha = \operatorname{Re}(a) \neq 0$ (no roots on the imaginary axis).
Look geometrically at the vector $i\omega - a = -\alpha + i(\omega - \beta)$ as $\omega$ goes from $-\infty$ to $+\infty$:

```text
Case 1: a in the RHP (α > 0)              Case 2: a in the LHP (α < 0)
-α < 0 (left of origin!)                  -α > 0 (right of origin!)

        Im ▲                                      Im ▲
  iω - a • │  (ω → +∞, angle → π/2)                │  • iω - a (ω → +∞, angle → +π/2)
         │ │                                       │  │
  ───────┼─┼────────► Re                    ───────┼──┼────────► Re
         │ │  sweeps                               │  │  sweeps
         │ │  CLOCKWISE (-π)                       │  │  CCW (+π)
  iω - a • │  (ω → -∞, angle → 3π/2)               │  • iω - a (ω → -∞, angle → -π/2)
```

* If $a$ is in the **RHP** ($\alpha > 0$), the point $i\omega - a$ moves upward along the vertical line $\operatorname{Re} = -\alpha < 0$ (to the *left* of the origin). Its angle goes from $3\pi/2$ down to $\pi/2$: a net change of **$-\pi$** (clockwise half-turn)!
* If $a$ is in the **LHP** ($\alpha < 0$), $i\omega - a$ moves upward along $\operatorname{Re} = -\alpha > 0$ (to the *right* of the origin). Its angle goes from $-\pi/2$ up to $+\pi/2$: a net change of **$+\pi$** (counterclockwise half-turn)!

In `ImagAxisIntegral.lean`, we verify this calculus-style without hand-waving by writing down the exact antiderivative:

$$\text{poleAntideriv}(a, \omega) = \frac{1}{2}\ln\!\left(\alpha^2 + (\omega - \beta)^2\right) - i \arctan\!\left(\frac{\omega - \beta}{\alpha}\right).$$

Differentiating gives **literally** $\frac{i}{i\omega - a}$! Evaluating from $-R$ to $+R$ and taking $R \to \infty$:
* The $\ln$-ratio $\frac{\alpha^2 + (R-\beta)^2}{\alpha^2 + (-R-\beta)^2} \to 1$, so the $\ln$ difference goes to $\ln 1 = 0$.
* The $\arctan$ terms go to $\pm\pi/2$, giving **$-i\pi$** when $\operatorname{Re}(a) > 0$, and **$+i\pi$** when $\operatorname{Re}(a) < 0$.

---

### Step C: Closing the Giant Semicircle (`SemicircleIntegral.lean`) & Why Properness Matters

Now look at the classic **Nyquist D-contour** of radius $R$ enclosing the right half-plane:

```text
               iR •
               ▲  │  ╲
               │  │     ╲   Right semicircle: s = R·e^(iθ),
   Upward      │  │       • θ goes from +π/2 down to -π/2
   imaginary   │  │       │ (clockwise!)
   axis        │  │       │
   [-iR, iR]   │  │     ╱
               │  │  ╱
              -iR •
```

Along the giant right semicircle $s = R e^{i\theta}$ ($\theta$ from $+\pi/2$ down to $-\pi/2$):
$$\frac{s'}{s - a} = \frac{i R e^{i\theta}}{R e^{i\theta} - a} = i + \frac{i a}{R e^{i\theta} - a}.$$
For $R > |a|$, the remainder has norm $\le \frac{|a|}{R - |a|} \to 0$. Integrating the constant $i$ from $\pi/2$ down to $-\pi/2$ gives:
$$\int_{\pi/2}^{-\pi/2} i\,d\theta = -i\pi$$
for **every** root $a$ (whether in the LHP or RHP)!

Now add the imaginary axis and the semicircle for one factor $a$:
* **If $a$ is in the RHP ($\operatorname{Re}(a) > 0$):** $(-i\pi) + (-i\pi) = -2\pi i$. Dividing by $-2\pi i$ (clockwise convention) gives **$+1$**! (Enclosed!)
* **If $a$ is in the LHP ($\operatorname{Re}(a) < 0$):** $(+i\pi) + (-i\pi) = 0$! (Not enclosed!)

Summing over all zeros of $D+N$ minus all poles of $D$ gives **`nyquist_dContour_tendsto`**, which holds **even for improper systems**:
$$\text{nyquistDContourCW}(R) \xrightarrow{R \to \infty} Z - P.$$

Now, **what if $L(s)$ is proper** (and non-degenerate: $\deg(D+N) = \deg D$, which holds automatically whenever $\deg N < \deg D$)?
Then $D + N$ and $D$ have the **exact same number of roots**! So on the outer semicircle, every zero contributes $-i\pi$ and every pole subtracts $-i\pi$: they cancel completely, and the semicircle integral goes to **$0$** (`nyquist_semicircle_tendsto_zero`)!

---

### Step D: Wait—Why Is the Integral Over ALL of $(-\infty, +\infty)$ Even Convergent?

Here is a subtle calculus trap that many textbooks gloss over, and why Lean forces us to be honest:
* A single term $\frac{i}{i\omega - a}$ decays like $\frac{1}{\omega}$ as $|\omega| \to \infty$. And $\int_{-\infty}^\infty \frac{1}{|\omega|}\,d\omega = \infty$! So a single pole term is **not** Lebesgue integrable!
* **The Rescue (`integrable_pole_sub_ref`):** When $\deg(D+N) = \deg D$, there are just as many zeros $z_j$ as poles $p_j$. We can subtract and re-add a reference pole $\frac{i}{i\omega - 1}$ from *each* zero and *each* pole—they cancel out identically! Each paired difference decays like $O(1/\omega^2)$:
  $$\frac{i}{i\omega - a} - \frac{i}{i\omega - 1} = \frac{i(a - 1)}{(i\omega - a)(i\omega - 1)} \le \frac{C}{1 + \omega^2}.$$
  Since $\frac{1}{1 + \omega^2}$ is integrable on $\mathbb{R}$, the whole `nyquistIntegrand` is genuinely **Lebesgue integrable** (`nyquistIntegrand_integrable`), and `nyquistEncirclementsCCW = P - Z` (`nyquist_encirclement_formula`) follows cleanly!

---

### Step E: Two Concrete Worked Examples (`Nyquist/Examples.lean`)
1. **Stable first-order loop:** $L(s) = \frac{K}{s+1}$ with $K > -1$.
   Open-loop pole at $s = -1$ ($P = 0$). Closed-loop root at $s = -(1+K) < 0$ ($Z = 0$). Nyquist encircles $-1$ **0 times** (`example1_nyquist_encirclements`).
2. **Stabilizing an unstable plant:** $L(s) = \frac{2}{s-1}$.
   Open-loop pole at $s = +1$ ($P = 1$!). Closed-loop polynomial is $(s-1) + 2 = s + 1$, root at $-1$ ($Z = 0$). So the closed loop **is** Hurwitz stable, and the Nyquist plot must wrap around $-1$ **once counterclockwise** ($N_{\text{CCW}} = 1$, $N_{\text{CW}} = -1$ — proved in `example2_nyquist_encirclements_ccw`)!

---

## 4. What About Integrators (Poles at $s = 0$)? (`Nyquist/Indentation.lean`)

Almost every real PI or PID controller has an integrator $\frac{1}{s}$—a pole sitting right on the imaginary axis at $s = 0$! You can't integrate straight through $0$ because $\frac{1}{i\omega}$ blows up.

**How `Indentation.lean` handles it:**
Just like in the textbook, we detour around $s = 0$ on a tiny right-half-plane semicircle of radius $\varepsilon > 0$ (so $0$ stays *outside* the enclosed RHP):

```text
          iR •
             ▲
          iε •
             │  ╲  tiny detour θ ∈ [-π/2, +π/2], radius ε
             │   •
         -iε •  ╱
             ▲
         -iR •
```

What happens to a pole $a = 0$ on this indented path?
1. On $[-R, -\varepsilon]$ and $[\varepsilon, R]$, the integrand is $\frac{i}{i\omega} = \frac{1}{\omega}$, which is an **odd function**! So the left piece and right piece cancel **identically to $0$** (`integral_origin_pole_imagAxis_cancel`)!
2. On the tiny semicircle $\varepsilon e^{i\theta}$ ($\theta : -\pi/2 \to +\pi/2$), $\frac{i\varepsilon e^{i\theta}}{\varepsilon e^{i\theta}} = i$ identically, so the integral is **exactly $+i\pi$** (`integral_origin_pole_indent`).
3. Every off-axis pole ($a \neq 0$) contributes an $O(\varepsilon)$ error on the tiny detour, which vanishes as $\varepsilon \to 0^+$ (`tendsto_indentPoleError`).

Notice that $+i\pi$ is the **exact same** value an LHP pole contributes! So every pole at $0$ matches one closed-loop pole as expected, giving `nyquist_indented_origin_criterion`—demonstrated on $L(s) = \frac{K}{s(s+1)}$ ($K > 0$) in `example_integrator_stable`.

---

## 5. General Argument Principle, Rouché, and Time-Delay Systems

### Meromorphic Argument Principle & Rouché (`Nyquist/ArgumentPrinciple.lean`)
Before tackling time delays, we prove the general function-theory workhorses directly on Mathlib's meromorphic infrastructure (`MeromorphicOn.extract_zeros_poles`):
* **`argumentPrinciple_circle`:** Around any circle $C(c, R)$, $\frac{1}{2\pi i}\oint \frac{f'}{f} = \sum (\text{zero orders}) - \sum (\text{pole orders})$.
* **`rouche_circle`:** If $|g(z)| < |f(z)|$ on the boundary circle, then $f + g$ and $f$ have the exact same net zero-minus-pole count inside. Instead of a complicated homotopy, we prove it in a few lines using $q(z) = 1 + g(z)/f(z)$: since $|g/f| < 1$, $\operatorname{Re}(q) > 0$, so $q$ stays away from the negative real axis (`Complex.slitPlane`), allowing a global continuous `Complex.log (q)` whose closed-loop integral is $0$!
* **`argumentPrinciple_rect`:** The exact same argument principle on **rectangles** (by computing the edge integrals of $(s - u)^{-1}$ explicitly with $\ln$ and $\arctan$ and watching the 4 corner logarithms cancel!).

### Why Rectangles Unlock Time-Delay Systems (`Nyquist/TimeDelay.lean`)
Now consider a retarded **time-delay system**:
$$L_\tau(s) = \frac{N(s)}{D(s)} e^{-\tau s}, \qquad \tau \ge 0, \qquad \deg N < \deg D.$$
Here $D(s) + N(s) e^{-\tau s} = 0$ has **infinitely many** roots in the complex plane, so polynomial factorization is dead. Why does Nyquist still work?!

Look at a large rectangle $[0, R] \times [-R, R]$ in the right half-plane:

```text
        0 + iR •───────────────• R + iR
               ▲               │
  Nyquist      │  RHP roots    │  On these 3 outer edges,
  axis         │  inside       │  Re(s) ≥ 0 so |exp(-τs)| ≤ 1,
  (ω: -R..R)   │  (only        │  and |N/D| → 0, hence
               │   finitely    │  Re(1 + L_τ(s)) > 0!
               │   many!)      │
        0 - iR •◄──────────────• R - iR
```

1. **Bounded in the RHP (`delayTransfer_rhp_bound`):** Whenever $\operatorname{Re}(s) \ge 0$ and $\tau \ge 0$, $|e^{-\tau s}| = e^{-\tau \operatorname{Re}(s)} \le 1$. Because $\deg N < \deg D$, $|N(s)/D(s)| \to 0$ as $|s| \to \infty$, so for large enough $R_0$, $|L_\tau(s)| < 1/2$ everywhere outside radius $R_0$ in the closed RHP!
2. **Only finitely many RHP zeros:** Because no RHP zero can live outside radius $R_0$, all closed-RHP zeros of $D(s) + N(s)e^{-\tau s}$ sit inside the compact box $[0, R_0] \times [-R_0, R_0]$—and isolated zeros on a compact set are always **finite**!
3. **The 3 outer edges vanish cleanly:** For $R > R_0$, on the bottom, right, and top edges of $[0, R] \times [-R, R]$, $|L_\tau(s)| < 1/2 \implies \operatorname{Re}(1 + L_\tau(s)) > 1/2 > 0$. So `1 + L_τ(s)` stays inside `Complex.slitPlane`, meaning `Complex.log (1 + L_τ(s))` is a valid antiderivative on all 3 outer edges! Their integrals telescope corner-to-corner to:
   $$\ln(1 + L_\tau(iR)) - \ln(1 + L_\tau(-iR)) \xrightarrow{R \to \infty} \ln 1 - \ln 1 = 0!$$
4. Applying **`argumentPrinciple_rect`** gives the full **Time-Delay Nyquist Theorem** (`nyquist_delay_stability_criterion`), plus the delay-independent **Small-Gain Theorem** (`nyquist_delay_small_gain`) and a concrete proof that $L_\tau(s) = \frac{1}{s+2} e^{-\tau s}$ is stable for **all** delays $\tau \ge 0$ (`example_delay_independent_stable`).

---

## 6. Small-Gain, Gain Margin & Pole-Zero Cancellation (`Nyquist/Margins.lean`)

* **Small-Gain Disk (`nyquist_small_gain_hurwitz`):** If the open-loop plant is Hurwitz stable and $\|L(i\omega)\| < 1$ for all $\omega \in \mathbb{R}$, then $\operatorname{Re}(1 + L(i\omega)) > 0$ everywhere—the curve stays inside the unit disk centered at $0$ and can never wrap around $-1$. Thus $D + N$ is Hurwitz stable.
* **Gain Margin (`nyquist_gain_margin`):** Suppose you scale your controller gain $k$ continuously from $0$ up to $K_{\max}$. As long as $1 + k L(i\omega)$ never hits $0$ (meaning $L(i\omega)$ never touches $-1/k$), the winding number $k \mapsto N_{\text{CW}}(k)$ varies **continuously** (proved by dominating the integrand uniformly by $C / (1 + \omega^2)$) yet can only take **integer** values! By the Intermediate Value Theorem, an integer-valued continuous function on $[0, K_{\max}]$ cannot jump—it stays stuck at $0$ for the entire interval, guaranteeing stability for all $k \in [0, K_{\max}]$!
* **No Hidden Cancellations (`coprime_no_rhp_cancellation`):** If $N$ and $D$ are coprime (`IsCoprime N D`), they share no roots at all, so $D$ and $D + N$ cannot silently cancel an unstable RHP pole.

---

## 7. What Do "Lean 4 Kernel" and "ZFC Axioms" Mean?

* **No hidden assumptions:** If you run `#print axioms` on any of the main theorems in `Nyquist/Examples.lean`, Lean prints:
  ```text
  [propext, Classical.choice, Quot.sound]
  ```
* These are Lean's three standard mathematical axioms:
  1. `propext` — logically equivalent propositions are equal;
  2. `Classical.choice` — standard Axiom of Choice (the "C" in ZFC set theory);
  3. `Quot.sound` — quotients work as expected (needed to build real numbers $\mathbb{R}$ cleanly).
* There is **no** `sorry`, no `admit`, no `native_decide` (unverified compiler evaluation), and no custom physics/math axioms anywhere in the project.
