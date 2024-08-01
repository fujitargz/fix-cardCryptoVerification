// Copyright (C) 2020 Michael Kirsten, Michael Schrempp, Alexander Koch

//    This program is free software; you can redistribute it and/or modify
//    it under the terms of the GNU General Public License as published by
//    the Free Software Foundation; either version 3 of the License, or
//    (at your option) any later version.

//    This program is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//    GNU General Public License for more details.

//    You should have received a copy of the GNU General Public License
//    along with this program; if not, <http://www.gnu.org/licenses/>.

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>

// unsigned int nondet_uint();
// void __CPROVER_assume(int x);
// void __CPROVER_assert(int x, char y[]);

// #define assert2(x, y) __CPROVER_assert(x, y)
// #define assume(x) __CPROVER_assume(x)

/**
 * Size of input sequence (number of cards including both commitments plus additional cards).
 */
#ifndef N
#define N 4
#endif

/**
 * Amount of distinguishable card symbols.
 */
#ifndef NUM_SYM
#define NUM_SYM 4
#endif


/**
 * Number of all cards used for commitments
 */
#ifndef COMMIT
#define COMMIT 4
#endif

/**
 * Protocol length.
 */
#ifndef L
#define L 5
#endif

/**
 * Amount of different action types allowed in protocol, excluding result action.
 */
#ifndef A
#define A 2
#endif

/**
 * Number assigned to turn action.
 */
#ifndef TURN
#define TURN 0
#endif

/**
 * Number assigned to shuffle action.
 */
#ifndef SHUFFLE
#define SHUFFLE 1
#endif

/**
 * Regarding possibilities for a sequence, we (only) consider
 * - 0: probabilistic security
 *      (exact possibilities for a sequence)
 * - 1: input possibilistic security (yes or no)
 *      (whether the sequence can belong to the specific input)
 * - 2: output possibilistic security (yes or no)
 *      (to which output the sequence can belong)
 */
#ifndef WEAK_SECURITY
#define WEAK_SECURITY 0
#endif

/**
 * We always had four input possibilities,
 * this is changed if we only consider output possibilistic security.
 * This variable is used for over-approximating loops such that
 * their unrolling bound can be statically determined.
 */
#if WEAK_SECURITY == 2
    #define NUMBER_PROBABILITIES 2
#else
    #define NUMBER_PROBABILITIES 4
#endif

/**
 * For two players inserting yes or no to a protocol,
 * there are four different possibilities how the protocol could start.
 * For more players or other scenarios this value has to be adapted.
 */
#ifndef NUMBER_START_SEQS
#define NUMBER_START_SEQS 4
#endif

/**
 * 1 is finite runtime, 0 is restart-free Las-Vegas.
 * NOTE: this feature is not implemented yet
 */
#ifndef FINITE_RUNTIME
#define FINITE_RUNTIME 0
#endif

/**
 * If set to 1, only closed protocols with closed shuffles will be searched.
 */
#ifndef CLOSED_PROTOCOL
#define CLOSED_PROTOCOL 0
#endif

/**
 * If set to 1, only protocols with random cuts will be searched.
 */
#ifndef FORCE_RANDOM_CUTS
#define FORCE_RANDOM_CUTS 0
#endif

/**
 * Maximum number of sequences (usually N!).
 * This value can be lowered if there are multiple indistinguishable symbols in the deck.
 * This variable is used for over-approximating loops such that
 * their unrolling bound can be statically determined.
 */
#ifndef NUMBER_POSSIBLE_SEQUENCES
#define NUMBER_POSSIBLE_SEQUENCES 24
#endif

/**
 * This variable is used to limit the permutation set in any shuffle.
 * This can reduce the running time of this program.
 * When reducing this Variable, keep in mind that it could exclude some valid protocols,
 * as some valid permutation sets are not longer considered.
 */
#ifndef MAX_PERM_SET_SIZE
#define MAX_PERM_SET_SIZE NUMBER_POSSIBLE_SEQUENCES
#endif

/**
 * After a turn, the protocol tree splits up in one subtree for each possible observation.
 * You can use these two variables for restricting the number of observations after every turn.
 * In our case, we exclude the "trivial turn" where the turned card is already known since the
 * protocol would not branch there. Therefore we force the program to have at least two branches
 * after every turn operation.
 */
#ifndef MIN_TURN_OBSERVATIONS
#define MIN_TURN_OBSERVATIONS 2
#endif

/**
 * See description of MIN_TURN_OBSERVATIONS above.
 */
#ifndef MAX_TURN_OBSERVATIONS
#define MAX_TURN_OBSERVATIONS NUM_SYM
#endif

/**
 * The number of states stored in the protocol run (Start state + all L derived states).
 */
#ifndef MAX_REACHABLE_STATES
#define MAX_REACHABLE_STATES L+1
#endif

struct fraction {
    unsigned int num; // The numerator.
    unsigned int den; // The denominator.
};

struct fractions {
    struct fraction frac[NUMBER_PROBABILITIES];
};

/**
 * This is one sequence, as seen from left to right.
 *
 * If the sequence can belong to a specific input sequence,
 * then the probabilities entry is set to the probability for this input sequence.
 * Indices:
 * - 0: X_00
 * - 1: X_01
 * - 2: X_10
 * - 3: X_11
 *
 * If the sequence is not contained in the state, all probabilities are set to zero.
 *
 * We save the probabilities as numerator/denominator (of type fraction),
 * so we can avoid floating point operations and divisions.
 *
 * One line looks like this:
 *   val:           [card#1][card#2]..[card#N]
 *   probs:         [num#1]..[num#4]
 *   (num./denom.)  [den#1]..[den#4]
 *
 * For input-possibilistic protocols,
 * we only need to determine whether a sequence can belong to a specific input:
 *    [card#1][card#2]..[card#N]
 *    [bool#1]..[bool#4]
 *
 * For output-possibilistic protocols,
 * we only need to determine whether a sequence can belong to a specific output:
 *    [card#1][card#2]..[card#N]
 *    [bool#1][bool#2]
 * Note that in this scenario, we have bool#1 == X_0 and bool#2 == X_1.
 */
struct sequence {
    unsigned int val[N];
    struct fractions probs;
};


/**
 * All sequences are remembered here, as seen from left to right, sorted alphabetically.
 * The states in this program are equal to the states in KWH trees.
 */
struct state {
    struct sequence seq[NUMBER_POSSIBLE_SEQUENCES];
};

/**
 * An integer array with length N.
 */
struct narray {
    unsigned int arr[N];
};

/**
 * We store one empty state at beginning of the program to save ressources.
 */
// struct state emptyState;
struct state emptyState = {
    1, 2, 3, 4, {0, 1, 0, 1, 0, 1, 0, 1},
    1, 2, 4, 3, {0, 1, 0, 1, 0, 1, 0, 1},
    1, 3, 2, 4, {0, 1, 0, 1, 0, 1, 0, 1},
    1, 3, 4, 2, {0, 1, 0, 1, 0, 1, 0, 1},
    1, 4, 2, 3, {0, 1, 0, 1, 0, 1, 0, 1},
    1, 4, 3, 2, {0, 1, 0, 1, 0, 1, 0, 1},
    2, 1, 3, 4, {0, 1, 0, 1, 0, 1, 0, 1},
    2, 1, 4, 3, {0, 1, 0, 1, 0, 1, 0, 1},
    2, 3, 1, 4, {0, 1, 0, 1, 0, 1, 0, 1},
    2, 3, 4, 1, {0, 1, 0, 1, 0, 1, 0, 1},
    2, 4, 1, 3, {0, 1, 0, 1, 0, 1, 0, 1},
    2, 4, 3, 1, {0, 1, 0, 1, 0, 1, 0, 1},
    3, 1, 2, 4, {0, 1, 0, 1, 0, 1, 0, 1},
    3, 1, 4, 2, {0, 1, 0, 1, 0, 1, 0, 1},
    3, 2, 1, 4, {0, 1, 0, 1, 0, 1, 0, 1},
    3, 2, 4, 1, {0, 1, 0, 1, 0, 1, 0, 1},
    3, 4, 1, 2, {0, 1, 0, 1, 0, 1, 0, 1},
    3, 4, 2, 1, {0, 1, 0, 1, 0, 1, 0, 1},
    4, 1, 2, 3, {0, 1, 0, 1, 0, 1, 0, 1},
    4, 1, 3, 2, {0, 1, 0, 1, 0, 1, 0, 1},
    4, 2, 1, 3, {0, 1, 0, 1, 0, 1, 0, 1},
    4, 2, 3, 1, {0, 1, 0, 1, 0, 1, 0, 1},
    4, 3, 1, 2, {0, 1, 0, 1, 0, 1, 0, 1},
    4, 3, 2, 1, {0, 1, 0, 1, 0, 1, 0, 1},
};

/**
 * Determines whether the sequence belongs to at least one input sequence.
 * This value is true iff the sequence could be generated from any of the protocol's
 * input sequeces through the currently executed actions.
 */
unsigned int isStillPossible(struct fractions probs) {
    unsigned int res = 0;
    for (unsigned int i = 0; i < NUMBER_PROBABILITIES; i++) {
        res |= probs.frac[i].num;
    }
    return res;
}

/**
 * Given an array containing a sequence, we return the index of the given sequence in a state.
 */
unsigned int getSequenceIndexFromArray(struct narray compare, struct state compareState) {
    // unsigned int seqIdx = nondet_uint();
    // assume (seqIdx < NUMBER_POSSIBLE_SEQUENCES);
    // struct sequence seq = compareState.seq[seqIdx];

    // for (unsigned int i = 0; i < N; i++) {
    //     assume (compare.arr[i] == seq.val[i]);
    // }
    for (unsigned int i = 0; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
        unsigned int seqIdx = i;
        struct sequence seq = compareState.seq[seqIdx];
        unsigned int match = 1;
        for (unsigned int j = 0; j < N; j++) {
            if (compare.arr[j] != seq.val[j]) {
                match = 0;
                break;
            }
        }
        if (match) {
            return seqIdx;
        }
    }
    return 0;
}

/**
 * Update the possibilities of a sequence after a shuffle.
 */
struct fractions recalculatePossibilities(struct fractions probs,
                                          struct fractions resProbs,
                                          unsigned int permSetSize) {
    for (unsigned int k = 0; k < NUMBER_PROBABILITIES; k++) {
        struct fraction prob = probs.frac[k];
        unsigned int num   = prob.num;
        unsigned int denom = prob.den;

        if (num && WEAK_SECURITY) {
            resProbs.frac[k].num |= num;
        } else if (num) {
            /**
             * Only update fractions in case we are in the
             * strong security setup.
             */
            // Update denominator.
            resProbs.frac[k].den = denom * permSetSize;
            // Update numerator.
            resProbs.frac[k].num = (num * permSetSize) + denom;
        }
    }
    return resProbs;
}

/**
 * Calculate the state after a shuffle operation starting from s with the given permutation set.
 */
struct state doShuffle(struct state s,
                       unsigned int permutationSet[MAX_PERM_SET_SIZE][N],
                       unsigned int permSetSize) {
    struct state res = emptyState;
    // For every sequence in the input state.
    for (unsigned int i = 0; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
        if (isStillPossible(s.seq[i].probs)) {
            // For every permutation in the permutation set.
            for (unsigned int j = 0; j < MAX_PERM_SET_SIZE; j++) {
                if (j < permSetSize) {
                    struct narray resultingSeq = { .arr = { 0 } };
                    for (unsigned int k = 0; k < N; k++) {
                        // Apply permutation j to sequence i.
                        resultingSeq.arr[permutationSet[j][k]] = s.seq[i].val[k];
                    }
                    printf("sequence     : ");
                    for (unsigned int l = 0; l < N; l++) {
                        printf("%d ", s.seq[i].val[l]);
                    }
                    printf(" ");
                    for (unsigned int l = 0; l < NUMBER_PROBABILITIES; l++) {
                        printf("%d/%d ", s.seq[i].probs.frac[l].num, s.seq[i].probs.frac[l].den);
                    }
                    printf("\npermutation  : ");
                    for (unsigned int l = 0; l < N; l++) {
                        printf("%d ", permutationSet[j][l]+1);
                    }
                    printf("\nresult       : ");
                    for (unsigned int l = 0; l < N; l++) {
                        printf("%d ", resultingSeq.arr[l]);
                    }
                    printf(" ");

                    unsigned int resultSeqIndex = // Get the index of the resulting sequence.
                        getSequenceIndexFromArray(resultingSeq, res);
                    // Recalculate possibilities.
                    res.seq[resultSeqIndex].probs =
                        recalculatePossibilities(s.seq[i].probs,
                                                 res.seq[resultSeqIndex].probs,
                                                 permSetSize);

                    for (unsigned int l = 0; l < NUMBER_PROBABILITIES; l++) {
                        printf("%d/%d ", res.seq[resultSeqIndex].probs.frac[l].num, res.seq[resultSeqIndex].probs.frac[l].den);
                    }
                    printf("\n\n");
                }
            }
        }
    }
    return res;
}

/**
 * Generate a nondeterministic permutation set and apply it to the given state.
 */
struct state applyShuffle(struct state s) {
    // Generate permutation set (shuffles are assumed to be uniformly distributed).
    // unsigned int permSetSize = nondet_uint();
    // assume (0 < permSetSize && permSetSize <= MAX_PERM_SET_SIZE);
    unsigned int permSetSize = 2;

    unsigned int permutationSet[MAX_PERM_SET_SIZE][N] = { 0 };
    unsigned int takenPermutations[NUMBER_POSSIBLE_SEQUENCES] = { 0 };
    /**
     * Choose permSetSize permutations nondeterministically. To achieve this,
     * generate a nondeterministic permutation index and get the permutation from this index.
     * No permutation can be chosen multiple times.
     */
    // unsigned int lastChosenPermutationIndex = 0;
    // for (unsigned int i = 0; i < MAX_PERM_SET_SIZE; i++) {
    //     if (i < permSetSize) { // Only generate permutations up to permSetSize.
    //         unsigned int permIndex = nondet_uint();
    //         // This ensures that the permutation sets are sorted lexicographically.
    //         assume (lastChosenPermutationIndex <= permIndex);
    //         assume (permIndex < NUMBER_POSSIBLE_SEQUENCES);
    //         assume (!takenPermutations[permIndex]);

    //         takenPermutations[permIndex] = 1;
    //         lastChosenPermutationIndex = permIndex;

    //         for (unsigned int j = 0; j < N; j++) {
    //             permutationSet[i][j] = s.seq[permIndex].val[j] - 1;
    //             /**
    //              * The '-1' is important. Later, we convert to array indices such as
    //              * array[permutationSet[x][y]]. Without the '-1', we would get out-
    //              * of-bound errors there.
    //              */
    //         }
    //     }
    // }
    for (unsigned int i = 0; i < N; i++) {
        permutationSet[0][i] = s.seq[0].val[i] - 1;
        permutationSet[1][i] = s.seq[6].val[i] - 1;
    }

    // if (CLOSED_PROTOCOL || FORCE_RANDOM_CUTS) { // Check for closedness.
    //     checkTransitivityOfPermutation(permutationSet, permSetSize);
    //     // As in state trees, we want to include the identity if it is not a permutation.
    //     assume (permSetSize == 1 || takenPermutations[0] > 0);
    // }
    // Apply the shuffle that was generated above.
    struct state res = doShuffle(s, permutationSet, permSetSize);

    // assume (isBottomFree(res));
    return res;
}

int main() {
    // a counterexample to correctness verification
    struct state startState = {
    // |  sequence  |probabilities (num/den)|
    // |            |X_00 |X_01 |X_10 |X_11 |
        1, 2, 3, 4, {1, 1, 1, 1, 1, 1, 0, 1}, // sequence 1
        1, 2, 4, 3, {0, 1, 0, 1, 0, 1, 0, 1},
        1, 3, 2, 4, {0, 1, 0, 1, 0, 1, 0, 1},
        1, 3, 4, 2, {0, 1, 0, 1, 0, 1, 1, 1}, // sequence 2
        1, 4, 2, 3, {0, 1, 0, 1, 0, 1, 0, 1},
        1, 4, 3, 2, {0, 1, 0, 1, 0, 1, 0, 1},
        2, 1, 3, 4, {0, 1, 0, 1, 0, 1, 0, 1},
        2, 1, 4, 3, {0, 1, 0, 1, 0, 1, 0, 1},
        2, 3, 1, 4, {0, 1, 0, 1, 0, 1, 0, 1},
        2, 3, 4, 1, {0, 1, 0, 1, 0, 1, 0, 1},
        2, 4, 1, 3, {0, 1, 0, 1, 0, 1, 0, 1},
        2, 4, 3, 1, {0, 1, 0, 1, 0, 1, 0, 1},
        3, 1, 2, 4, {0, 1, 0, 1, 0, 1, 0, 1},
        3, 1, 4, 2, {0, 1, 0, 1, 0, 1, 0, 1},
        3, 2, 1, 4, {0, 1, 0, 1, 0, 1, 0, 1},
        3, 2, 4, 1, {0, 1, 0, 1, 0, 1, 0, 1},
        3, 4, 1, 2, {0, 1, 0, 1, 0, 1, 0, 1},
        3, 4, 2, 1, {0, 1, 0, 1, 0, 1, 0, 1},
        4, 1, 2, 3, {0, 1, 0, 1, 0, 1, 0, 1},
        4, 1, 3, 2, {0, 1, 0, 1, 0, 1, 0, 1},
        4, 2, 1, 3, {0, 1, 0, 1, 0, 1, 0, 1},
        4, 2, 3, 1, {0, 1, 0, 1, 0, 1, 0, 1},
        4, 3, 1, 2, {0, 1, 0, 1, 0, 1, 0, 1},
        4, 3, 2, 1, {0, 1, 0, 1, 0, 1, 0, 1},
    };

    for (int i = 0; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
        if(!isStillPossible(startState.seq[i].probs)) {
            continue;
        }
        printf("%d %d %d %d  ", startState.seq[i].val[0], startState.seq[i].val[1], startState.seq[i].val[2], startState.seq[i].val[3]);
        printf("%d/%d ", startState.seq[i].probs.frac[0].num, startState.seq[i].probs.frac[0].den);
        printf("%d/%d ", startState.seq[i].probs.frac[1].num, startState.seq[i].probs.frac[1].den);
        printf("%d/%d ", startState.seq[i].probs.frac[2].num, startState.seq[i].probs.frac[2].den);
        printf("%d/%d\n", startState.seq[i].probs.frac[3].num, startState.seq[i].probs.frac[3].den);
    }
    printf("\n---shuffle---\n");

    struct state s = applyShuffle(startState);

    printf("---state after shuffle---\n");
    for (int i = 0; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
        if(!isStillPossible(s.seq[i].probs)) {
            continue;
        }
        printf("%d %d %d %d  ", s.seq[i].val[0], s.seq[i].val[1], s.seq[i].val[2], s.seq[i].val[3]);
        printf("%d/%d ", s.seq[i].probs.frac[0].num, s.seq[i].probs.frac[0].den);
        printf("%d/%d ", s.seq[i].probs.frac[1].num, s.seq[i].probs.frac[1].den);
        printf("%d/%d ", s.seq[i].probs.frac[2].num, s.seq[i].probs.frac[2].den);
        printf("%d/%d\n", s.seq[i].probs.frac[3].num, s.seq[i].probs.frac[3].den);
    }

    return 0;
}
