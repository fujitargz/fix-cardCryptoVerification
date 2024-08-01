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

unsigned int nondet_uint();
void __CPROVER_assume(int x);
void __CPROVER_assert(int x, char y[]);

#define assert2(x, y) __CPROVER_assert(x, y)
#define assume(x) __CPROVER_assume(x)

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
 * We use this struct to return arrays of states after turn operations.
 * There is one state for each possible observation.
 * In each turn, each sequence with an observable card #X is stored in
 * state X-1 and moreover isUsed[X-1] == 1 holds.
 * If a card Y cannot be observed in the turn operation, then isUsed[Y-1] == 0 must hold.
 */
struct turnStates {
    struct state states[MAX_TURN_OBSERVATIONS];
    unsigned int isUsed[MAX_TURN_OBSERVATIONS];
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


struct turnStates alignAndAssignFractions(struct turnStates result,
                                          struct fractions probs) {
    for (unsigned int i = 0; i < MAX_TURN_OBSERVATIONS; i++) {
        if (result.isUsed[i]) {
            unsigned int newDenominator = 1;
            /**
             * Align all fractions to the same denominator,
             * such that the sum of all fractions is again == 1.
             * This denominator is not yet stored in the arrays,
             * since we might need the old denominators later-on to reduce the fractions!
             */
            for (unsigned int j = 0; j < NUMBER_PROBABILITIES; j++) {
                for (unsigned int k = 0; k < NUMBER_PROBABILITIES; k++) {
                    if (k != j) {
                        probs.frac[j].num *= probs.frac[k].den;
                    }
                }
                // Only accept states with equal possibilities.
                // assume (probs.frac[j].num == probs.frac[0].num);
                if (probs.frac[j].num != probs.frac[0].num) {
                    printf("%s\n", "security is not satisfied.");
                    return result;
                }
                newDenominator *= probs.frac[j].den;
            }
            // Update fractions in result state.
            for (unsigned int j = 0; j < NUMBER_POSSIBLE_SEQUENCES; j++) {
                for (unsigned int k = 0; k < NUMBER_PROBABILITIES; k++) {
                    result.states[i].seq[j].probs.frac[k].num *= newDenominator;
                    result.states[i].seq[j].probs.frac[k].den *= probs.frac[k].num;
                }
            }
        }
    }
    printf("%s\n", "security is satisfied.");
    return result;
}

struct fractions computeTurnProbabilities(struct turnStates result) {
    struct fractions probs;
    for (unsigned int i = 0; i < NUMBER_PROBABILITIES; i++) {
        probs.frac[i].num = 0;
        // We later want to multiply all denominators with each other.
        probs.frac[i].den = 1;
    }

    for (unsigned int i = 0; i < MAX_TURN_OBSERVATIONS; i++) {
        if (result.isUsed[i]) { // Only recalculate states that are used later.
            struct state resultState = result.states[i];
            // Add up all possibilities in a state.
            for (unsigned int j = 0; j < NUMBER_POSSIBLE_SEQUENCES; j++) {
                struct sequence resultSeq = resultState.seq[j];
                if (isStillPossible(resultSeq.probs)) {
                    for (unsigned int k = 0; k < NUMBER_PROBABILITIES; k++) {
                        struct fraction prob = resultSeq.probs.frac[k];
                        unsigned int num   = prob.num;
                        unsigned int denom = prob.den;
                        unsigned int newNum   = probs.frac[k].num;
                        unsigned int newDenom = probs.frac[k].den;
                        /**
                         * If the sequence does not belong to an input sequence,
                         * this sequence should not be updated in this step.
                         */
                        if (num && denom == newDenom) {
                            probs.frac[k].num += num;
                        } else if (num && denom != newDenom) {
                            probs.frac[k].num = (newNum * denom) + (num * newDenom);
                            probs.frac[k].den *= denom;
                        }
                    }
                }
            }
        }
    }
    return probs;
}

/**
 * Given state and the position of a turned card,
 * this function returns all branched states resulting from the turn.
 */
struct turnStates copyObservations(struct state s, unsigned int turnPosition) {
    struct turnStates result;
    // Initialise N empty states.
    for (unsigned int i = 0; i < MAX_TURN_OBSERVATIONS; i++) {
        result.states[i] = emptyState;
        result.isUsed[i] = 0;
    }
    unsigned int cntTurnObservations = 0;
    /**
     * If a sequence belongs to an observation X, then copy this
     * sequence into the state of observation X.
     */
    for (unsigned int i = 0; i < NUMBER_POSSIBLE_SEQUENCES; i++) {
        struct sequence seq = s.seq[i];
        if (isStillPossible(seq.probs)) {
            unsigned int turnedCardNumber = seq.val[turnPosition];
            unsigned int turnIdx = turnedCardNumber - 1;
            cntTurnObservations += result.isUsed[turnIdx] ? 0 : 1;
            result.isUsed[turnIdx] = 1;
            // assume (cntTurnObservations <= MAX_TURN_OBSERVATIONS);

            for (unsigned int j = 0; j < NUMBER_PROBABILITIES; j++) {
                struct fraction prob = seq.probs.frac[j];
                // Copy numerator.
                result.states[turnIdx].seq[i].probs.frac[j].num = prob.num;
                if (!WEAK_SECURITY) { // Probabilistic security
                    // Copy denominator.
                    result.states[turnIdx].seq[i].probs.frac[j].den = prob.den;
                }
            }
        }
    }

    // assume (MIN_TURN_OBSERVATIONS <= cntTurnObservations);
    return result;
}

/**
 * Turn at a nondeterministic position and return all resulting states. For each possible
 * observation, there is a distinct state. If an observation cannot occur through this
 * turn operation, the according isUsed entry is set to zero. For more information, refer
 * to the documentation of "turnStates".
 */
struct turnStates applyTurn(struct state s) {
    // Choose turn position nondeterministically, otherwise we cannot do two turns in a row.
    // unsigned int turnPosition = nondet_uint();
    // assume (turnPosition < N);
    unsigned int turnPosition = 0;

    struct turnStates result = copyObservations(s, turnPosition);
    if (WEAK_SECURITY) { // Weaker security check: output-possibilistic or input-possibilistic.
        for (unsigned int stateNumber = 0; stateNumber < MAX_TURN_OBSERVATIONS; stateNumber++) {
            if (result.isUsed[stateNumber]) {
                struct state resultState = result.states[stateNumber];
                // Now nondeterministic. We only need to find one sequence for
                // every possible in-/output. We assume nondeterministically
                // that the state contains a sequence for every in-/output possibility.
                for (unsigned int i = 0; i < NUMBER_PROBABILITIES; i++) {
                    unsigned int seqIndex = nondet_uint();
                    assume (seqIndex < NUMBER_POSSIBLE_SEQUENCES);
                    assume (resultState.seq[seqIndex].probs.frac[i].num);
                }
            }
        }
    } else { // Probabilistic security.
        struct fractions probs = computeTurnProbabilities(result);
        // print the value of rho
        printf("calculated value of rho: ");
        for (unsigned int i = 0; i < NUMBER_PROBABILITIES; i++) {
            printf("%d/%d ", probs.frac[i].num, probs.frac[i].den);
        }
        printf("\n");
        result = alignAndAssignFractions(result, probs);
    }

    return result;
}

int main() {
    // a counterexample to security verification
    struct state startState = {
    // |  sequence  |probabilities (num/den)|
    // |            |X_00 |X_01 |X_10 |X_11 |
        1, 2, 3, 4, {1, 3, 0, 1, 0, 1, 0, 1},
        1, 2, 4, 3, {0, 1, 1, 3, 0, 1, 0, 1},
        1, 3, 2, 4, {0, 1, 0, 1, 0, 1, 0, 1},
        1, 3, 4, 2, {0, 1, 0, 1, 1, 3, 0, 1},
        1, 4, 2, 3, {0, 1, 0, 1, 0, 1, 0, 1},
        1, 4, 3, 2, {0, 1, 0, 1, 0, 1, 0, 1},
        2, 1, 3, 4, {0, 1, 0, 1, 0, 1, 0, 1},
        2, 1, 4, 3, {0, 1, 0, 1, 0, 1, 1, 3},
        2, 3, 1, 4, {0, 1, 0, 1, 0, 1, 0, 1},
        2, 3, 4, 1, {1, 3, 0, 1, 0, 1, 0, 1},
        2, 4, 1, 3, {0, 1, 0, 1, 0, 1, 0, 1},
        2, 4, 3, 1, {0, 1, 1, 3, 0, 1, 0, 1},
        3, 1, 2, 4, {0, 1, 0, 1, 0, 1, 0, 1},
        3, 1, 4, 2, {0, 1, 0, 1, 0, 1, 0, 1},
        3, 2, 1, 4, {0, 1, 0, 1, 0, 1, 1, 3},
        3, 2, 4, 1, {0, 1, 0, 1, 0, 1, 0, 1},
        3, 4, 1, 2, {1, 3, 0, 1, 0, 1, 0, 1},
        3, 4, 2, 1, {0, 1, 0, 1, 1, 3, 0, 1},
        4, 1, 2, 3, {0, 1, 0, 1, 0, 1, 0, 1},
        4, 1, 3, 2, {0, 1, 0, 1, 0, 1, 0, 1},
        4, 2, 1, 3, {0, 1, 0, 1, 1, 3, 0, 1},
        4, 2, 3, 1, {0, 1, 0, 1, 0, 1, 0, 1},
        4, 3, 1, 2, {0, 1, 1, 3, 0, 1, 0, 1},
        4, 3, 2, 1, {0, 1, 0, 1, 0, 1, 1, 3},
    };

    printf("---state---\n");
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

    struct turnStates possiblePostStates = applyTurn(startState);

    for (int i = 0; i < MAX_TURN_OBSERVATIONS; i++) {
        if (possiblePostStates.isUsed[i]) {
            printf("\n---observation %d---\n", i+1);
            for (int j = 0; j < NUMBER_POSSIBLE_SEQUENCES; j++) {
                struct sequence seq = possiblePostStates.states[i].seq[j];
                if(!isStillPossible(seq.probs)) {
                    continue;
                }
                printf("%d %d %d %d  ", seq.val[0], seq.val[1], seq.val[2], seq.val[3]);
                printf("%d/%d ", seq.probs.frac[0].num, seq.probs.frac[0].den);
                printf("%d/%d ", seq.probs.frac[1].num, seq.probs.frac[1].den);
                printf("%d/%d ", seq.probs.frac[2].num, seq.probs.frac[2].den);
                printf("%d/%d\n", seq.probs.frac[3].num, seq.probs.frac[3].den);
            }
        }
    }
    return 0;
}
