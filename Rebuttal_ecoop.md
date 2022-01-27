# OVERVIEW: 

Many thanks to our reviewers for their interest and appreciation of certain aspects of our work. 

We acknowledge our weakness in the paper presentation. 
Thanks again for the time and effort in pointing out our typos and giving out constructive suggestionss. 

We took all the valuable comments into account and made the following change list. 


# CHANGE LIST: 


| | Changes     | Description | Timeline (Working days)    |
| ---  | ----------- | ----------- | ----------- |
|1 | Typos       | Mentioned in the reviews  | Already Done| 
|2 | Algorithm 1 | Replace it using inference rules  | 3-5 days    |
|3 | Introduction| Less technical with more details | 1-3 days | 
|4 | Section 2   |  Reduce explanations for Esterel, add more for Hiphop.js, to be more self-contained    |1-3 days | 
|5 | Section 3  | Emphasis the challenges we are facing |1-3 days | 
|6 | Case study | Emphasis the expressiveness by adding useful property examples  | 1-2 days (Partly done in Q2 to Reviewer A) |
|7 | Evaluation data | Have a table detailing summary statistics | 3 days |
|  | In total  | | 10 - 19 days

There are more minor adjustments to be done within 5 days :

- Drop the organization paragraph; 
- Reduce the unnecessary footnotes; 
- Provide (at least informal) definitions for terms at the first-mentioned site. In particular, for TRS, partial derivatives, SyncEff.
- Find a buddy to check the writings; 

In total, we plan to finish all the changes within 19+5=24 working days. 



# RESPONSE: 

## To Reviewer A

### Q1. Which aspects of your formalism build on previous work, and which are novel to this submission?

1. The syntax definition is the first core language for the mixed synchronous/asynchronous paradigm, although both were defined separately before. 

2. Since the syntax combination is new, the operational semantics is built on top of Esterel, so the ones with (Async) (Await) and (Call) are new. 

3. The trace inference rules presented in Sec 5.1 are entirely novel. 

4. For the back-end TRS, in the functions: nullable, first, derivatives, all the definitions for the waiting operator (?) and asynchronous parallel (||) are novels. 

5. The temporal verification framework is novel compared to traditional automata-based model checking. 


### Q2. What were the key technical challenges you faced?

Among all the challenges we faced, implementing the parallel merging algorithm took us the longest. 
The concept of linear synchronous parallelism is not so complicated. 
However, the Kleene stars make it complex. For example 
$(\{A\}.\{B\})^* || (\{C\}. \{D\}. \{E\})^*$, we should be able to find a fixpoint, which is 
$(\{A,C\}.\{B, D\}.\{A, E\}.\{B, C\}.\{A, D\}.\{B, E\})^*$. 

Luckily we manage to do that in our final implementation. 





### Q3. What are the sorts of properties you would like to check in a typical HipHop.js program?

Our proposed specification conveniently fuses traditional linear temporal logics, such as LTL. 

| LTL         | SyncEffs    | Description |
| ----------- | ----------- | ----------- |
| $\mathcal{F} (A)$ | $\{\}^*{\cdot}\{A\}$      | Finially A  (Safty) | 
| $\mathcal{G} (A)$ | $\{A\}^*$      | Globally A (Liveliness) | 
| $A\ \mathcal{U}  B$ | $\{A\}^*{\cdot}\{B\}$ | A until B
| $\mathcal{X} (A)$ | $\{\}{\cdot}\{A\}$  | Next A
| $A \rightarrow B$ | $\{\overline{A}\} \vee \{A, B\}$ |  Implication
| $\mathcal{F\ G} (A)$ | $\{\}^*{\cdot}\{A\}^*$  | Finially globally A
| $\mathcal{G\ F} (A)$ | $(\{\}^*{\cdot}\{A\})^*$  | Globally finially  A

(Here A and B are signals emitted from the program)



### Q4. Were there any surprises or challenges in the implementation/evaluation?

We preferred to make use of existing implementations to build our front-end. We looked into the source code of the compiler of Hiphop.js. Unfortunately, we did not manage to get it run. Due to the time limits, we wrote the parser from scratch in Ocaml for the core language. 

If there are follow-up works, we will continue to investigate adding our temporal verification into existing language implementations. 

Another surprise is the proof for the loop invariant inference we discovered (FV-Par rule and the proof in Appendix C), which has not been mentioned by prior works at all!


### Q5. Why not some evaluation statistics?

We spent some time building a reactive demo page. 
Users can choose test cases and run the verification on our server. 
There are verification time and proving details; one example can be found in the response Q2 to Reviewer B.

We did not cite the demo page to be anonymous. We will consider making a summary table to present some of them on the paper for further resubmissions. 
Thanks for the suggestion. 





## To Reviewer B 


### Q1. Can you expand on how you validated the verifier? In particular, what is the nature of the programs used, how they were selected, how were the annotations added.

We chose the program by needs of validating our novel ideas and challenging implementations: 

1. The loop invariant inference (FV-Loop): We proved (by inductive cases in Appendix C) the correctness of the loop invariant inference algorithm. 
2. The Async/Await rules (FV-Await and FV-Async): They are newly proposed in this paper. 
3. The parallel merging algorithm (FV-Par): Although the conceptual synchronous parallel is simple, the implementation is challenging. (Details see the response Q2 To Reviewer A)

Therefore, we chose test cases related to each of the above constructs, and we produced some other test cases involving combinations of the above constructs. 

We annotate the specifications by hand, based on the behaviors defined by the Esterel Compilers and Esterel semantics documentations. 


### Q2. How are the LHS/RHS from Fig. 9 provided? Are they deduced automatically from the program or do they need to be encoded by the developer?

While verifying a program, the LHS/RHS are deducted automatically from the program. 
The inclusion checkings are triggered: i) before function calls to check precondition; ii) by the end of the
verifying a function to check the postcondition. One example from the paper is Figure 5, step 10. which checks the function postcondition. 

However, one can use the back-end TRS independently. Our implementation includes an inclusion parser, which triggers the TRS directly. 
One example input and its corresponding TRS output:
```
({A, D, C})*.{} \/ {B}.({A})* |- ({})* \/ ({A,B})*;

----------------------------------------
((({A,D,C,})* . {}) . ({A,})*) \/ ({B,} . ({A,})*) |- ({})* \/ ({A,B,})*
[Result] Succeed
[Verification Time: 0.000132 s]
 

* ((({A,D,C,})* . {}) . ({A,})*) \/ ({B,} . ({A,})*) |- ({})* \/ ({A,B,})*   [UNFOLD]
* ├── ({A,})* |- ({})*   [UNFOLD]
* │   └── ({A,})* |- ({})*   [Reoccur]
* ├── ({A,})* |- ({})*   [UNFOLD]
* │   └── ({A,})* |- ({})*   [Reoccur]
* └── ((({A,D,C,})* . {}) . ({A,})*) \/ (emp . ({A,})*) |- ({})*   [UNFOLD]
*     ├── ({A,})* |- ({})*   [UNFOLD]
*     │   └── ({A,})* |- ({})*   [Reoccur]
*     ├── ({A,})* |- ({})*   [UNFOLD]
*     │   └── ({A,})* |- ({})*   [Reoccur]
*     └── (({A,D,C,})* . ({} . ({A,})*)) \/ ({A,})* |- ({})*   [UNFOLD]
*         ├── ({A,})* |- ({})*   [UNFOLD]
*         │   └── ({A,})* |- ({})*   [Reoccur]
*         ├── ({A,})* |- ({})*   [UNFOLD]
*         │   └── ({A,})* |- ({})*   [Reoccur]
*         └── (({A,D,C,})* . ({} . ({A,})*)) \/ ({A,})* |- ({})*   [Reoccur]
```


### Q3. why d+2 instead of 2, if any code >2 is considered as an error?

The completion code k originated from prior works defining semantics for Esterel. 
We find this is an intelligent design as in:

Given a program p, for a small step evaluation to p':

- k = 0, means there are no exceptions.
- k = 1, means there are no exceptions, but a pause (L348).
- k = 2, there is an exception, which escapes the nearest try-catch. 
- k > 2, means there is an exception, which escapes a further nesting try-catch. 

Therefore, if we write "raise 0" to escape the nearest try-catch, the completion code should be k = 0+2. 







## To Reviewer C

### Q1. What about something like "Temporal Verification of Synchronous and Asynchronous Concurrency."

That looks good! Thanks for the suggestion. 

### Q2. what is a back-end TRS?

TRS means the term rewriting system we developed. It is used as a back-end solver for our verification. 

### Q3. l66 soundly check can you unsoundly check?

If the algorithm is unsound, it will validate an invalid inclusion input. 
We meant that our algorithm is proven sound. 


### Q4. what about $\lambda^{a/s}$ ?

$\lambda^{a/s}$  sounds good! Thanks for the suggestion.


---


Thank you so much for all the constructive suggestions. 


Best, 

Authors from Submission #53