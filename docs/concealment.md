# Concealment of gaps

When frames of a stream are missing at the time they are due, the receiver
plays something in their place. This page states what is to be computed as a
problem of inference, says which instance of that problem the code solves
today, and compares it with the alternatives. It is meant to be read before a
scheme is changed or added.

Concealment is one module of a receiver. A scheme sees every frame of the
stream in order, each either as a frame that arrived or as a place where one
is missing, and writes what is played. In `crates/unisono-dsp` that is the
pair of functions `Concealment::pass` and `Concealment::fill`. A different
scheme takes its place by offering the same two.

## The problem

Let $x$ be the signal the sender captured, $x_{\text{past}}$ the samples
before a gap, which the receiver has played, and $x_{\text{gap}}$ the missing
ones. A scheme computes an estimate $\hat x_{\text{gap}}$ from what it knows.
Four choices define a scheme.

1. **What is known.** At the lowest latency only $x_{\text{past}}$: a missing
   sample is due before anything after it has arrived. A receiver that holds
   its output back also knows the samples after the gap,
   $x_{\text{after}}$, when it fills the gap.
2. **The model of the signal**, a distribution $p(x \mid \theta)$ with
   parameters $\theta$. For a Gaussian model it is a covariance, or
   equivalently a filter $A_\theta$ that turns the signal into white noise:
   $-\log p(x \mid \theta) = \lVert A_\theta x\rVert^2 / 2\sigma^2$ plus a
   constant, with $\sigma^2$ the power of that noise.
3. **How the parameters are found** from the samples before the gap: a
   criterion of fit, and what keeps the fit from following the noise in a
   short record, which is the regularization.
4. **Which estimate is played** under the fitted model: the one that
   minimizes an expected loss. For the squared error it is the mean of
   $p(x_{\text{gap}} \mid \text{what is known}, \hat\theta)$.

With a Gaussian model and the squared error, the estimate is the solution of

$$\hat x_{\text{gap}} \;=\; \arg\min_{x_{\text{gap}}}\;
\lVert A_{\hat\theta}\,x\rVert^2
\quad\text{with the known samples of } x \text{ held fixed}.$$

Nothing is measured inside the gap, so this problem has no data term there:
the known samples enter as constraints, and the model is the only thing that
says what lies between or beyond them.

## What the code solves today

The model is autoregressive: a sample is a weighted sum of the `order`
samples before it plus white noise. $A_\theta$ is then the filter that
subtracts that weighted sum, and $\theta$ are the weights. The sizes at
48 000 frames per second are an order of 32, fitted to the last 10 ms, for
each channel by itself.

**The fit is Burg's method.** It does not minimize the prediction error over
all weights at once. It builds the model one stage at a time. Stage $m$ has
the errors of predicting each sample forward from the $m-1$ samples before it,
$f_{m-1}[n]$, and backward from the $m-1$ samples after it, $b_{m-1}[n]$, and
chooses one number $k_m$ to minimize

$$\sum_n \bigl(f_{m-1}[n] + k_m\,b_{m-1}[n-1]\bigr)^2
+ \bigl(b_{m-1}[n-1] + k_m\,f_{m-1}[n]\bigr)^2 ,$$

with the earlier stages left as they are. The minimizer always satisfies
$|k_m| \le 1$, and a model built from such numbers has a response that does
not grow. The regularization is this structure, and the order: there is no
penalty term. Among stationary Gaussian signals that agree on the first
`order` lags of the autocorrelation, the autoregressive one is the one of
largest entropy, which is the sense in which the model assumes nothing more
than those lags.

**The estimate is the mean under that model given the past.** With only the
past held fixed, the minimum of $\lVert A x\rVert^2$ over the gap is zero in
the gap: each missing sample is the weighted sum of the samples before it,
computed one after another.

**The fades are not part of the optimization.** The continuation is
multiplied by a raised cosine that reaches silence after 20 ms, it is kept
within the largest sample of the fitted frames, and arriving frames are
cross-faded with it over 5 ms. Under the fitted model the mean needs none of
this. The fades stand for what the model leaves out: the weights are uncertain
after 480 samples, and sound does not stay the same for long.

Measured, at 48 000 frames per second with these sizes: a steady tone of
50 Hz or more is continued within 2 % of its amplitude over the first
millisecond and within 10 % over the first two; after 5 ms the error can be
half the amplitude. Noise-like sound and several close partials die away
within a few frames. The fit costs some tens of microseconds for a channel.

## The alternatives

Each row changes one of the four choices.

| Choice | Alternative | For it | Against it |
|---|---|---|---|
| Fit | All weights at once, by least squares on the forward and backward errors | Exact for a sum of tones, where Burg's stagewise fit has an error that depends on the phase of the tone in a short record | Without a constraint the model can have a growing response. Tried on sounds of many close partials, it gave continuations up to several hundred times the level within 10 ms |
| Fit | The same with a penalty $\lambda\lVert\theta\rVert^2$, then moving any growing part of the response inside the stable range | Keeps the exactness for tones as $\lambda \to 0$ and bounds the growth. The penalty is the assumption that the signal contains white noise of power $\lambda$ | One more number to choose, and a root-finding or step-down pass to enforce stability. Not built, not measured |
| Model | A term for a long lag beside the short ones | An order of 32 at 48 000 frames per second spans 0.67 ms. It describes the spectrum, not the repetition of a waveform with a period of 2 to 20 ms, which is what continues a voice or a single instrument | The lag has to be found, costs more, and is wrong for sound without one period |
| Model | A longer record and a higher order | Resolves low tones: 10 ms holds one cycle of 100 Hz | Sound changes within tens of milliseconds, so a longer record fits a signal that is no longer there; the cost grows with the product of the two |
| Estimate | A sample from the distribution instead of its mean, by driving the model with noise of the fitted power | The mean of a noise-like signal is close to zero after a few samples, so the level dips. A sample keeps level and spectrum. The squared error is not what the ear judges | Wrong for tones, where the mean is right; the two would have to be mixed by how predictable the signal is. Makes the output depend on a random sequence, which then has to be a seeded one |
| What is known | Both sides of the gap: minimize $\lVert A x\rVert^2$ with the samples before and after held fixed, a banded linear system for the gap | An interpolation is far more accurate than a continuation, and it meets the arriving frames without a cross-fade | The output has to be held back by the length of the gaps to be filled. That is latency, and belongs with the weights of the objective in `docs/model.md` |
| Fades | Derive the shrinkage from the uncertainty of the fit, in place of a fixed raised cosine | The level would follow how predictable the sound is: a steady tone could be held longer, noise dropped sooner | Needs the distribution of the weights given the record, which Burg's method does not give |

## What a comparison needs

A scheme is judged on recordings and on synthetic signals with known
continuations: steady tones across the band, sums of close partials, noise,
and signals that change within the fitted record. The squared error of the
first milliseconds is one figure; the level and spectrum of what is played
through the gap are others, since a continuation that is wrong but sounds
like the stream can be better than one that is right on average and silent.
None of these comparisons has been run beyond the figures above.
