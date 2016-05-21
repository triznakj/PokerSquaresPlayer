import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Stack;

public class TrizPlayer implements PokerSquaresPlayer {
	class InfoBomb {
		public Card[] hand;
		public int maxRank;
		public int minRank;
		public boolean evenSuit;
		public boolean duplicates;
		public int numDuplicates;
		public boolean triples;
		public int size;
		public HashMap<Integer, Integer> amts;
		public boolean quads;
		public float percent;
		public int theEvenSuit;
		public ArrayList<Card> deck;

		public InfoBomb(Card[] hand, ArrayList<Card> deck) {
			this.deck = deck;
			this.hand = hand;
			size = 0;
			quads = false;
			maxRank = -1;
			minRank = 100;
			evenSuit = true;
			int testSuit = -1;
			duplicates = false;
			numDuplicates = 0;
			triples = false;
			amts = new HashMap<Integer, Integer>();
			for (int i = 0; i < SIZE; i++) {
				if (hand[i] != null) {
					// Increment size
					// System.out.print(" ["+hand[i].toString() + "] ");
					size++;
					int rank = hand[i].getRank();
					// Increment hand's max/min cards
					maxRank = Integer.max(maxRank, rank);
					minRank = Integer.min(minRank, rank);
					// check for suit (flush potentials)
					if (testSuit != hand[i].getSuit() && testSuit != -1) {
						evenSuit = false;
					} else {
						testSuit = hand[i].getSuit();
						theEvenSuit = hand[i].getSuit();
					}
					// duplicates and triples
					if (amts.containsKey(rank)) {
						amts.put(rank, amts.get(rank) + 1);
					} else {
						amts.put(rank, 1);
					}
				} else {
					// System.out.print(" [  ] ");
				}
			}
			// System.out.println(" ");
			percent = (float) size / (float) SIZE;
			for (int i : amts.keySet()) {
				if (amts.get(i) == 2) {
					duplicates = true;
					numDuplicates++;
				}
				if (amts.get(i) == 3) {
					triples = true;
				}
				if (amts.get(i) == 4) {
					quads = false;
				}
			}
		}

		public void PrintHand() {
			for (int i = 0; i < SIZE; i++) {
				if (hand[i] == null) {
					System.out.print(" [] ");
				} else {
					System.out.print(" [" + hand[i].toString() + "] ");
				}
			}
			System.out.print("\n");
		}
	}

	private int SIZE = 5;
	private Stack<Integer> plays = new Stack<Integer>();
	private Stack<Integer> temp = new Stack<Integer>();
	private int cardsInPlay = 0;
	private Card[][] grid = new Card[SIZE][SIZE];
	private Card[] deck = Card.getAllCards();
	private ArrayList<Card> simDeck;
	private PokerSquaresPointSystem system; // point system
	private double GreedyResult = 0;
	private int highCardScore;
	private double POTENTIAL_WEIGHT = .75;
	private long startMillis;
	private long millis;
	private int iterations;
	// Do you feel lucky...punk? (probability threshold for continuing to pursue
	// a hand)
	private double RF_DIRTY_HARRY = 0.2;
	private int DEPTH_THRESHOLD = 100;
	private int maxChoose;
	private int minChoose;
	private int maxChoosee;
	private int minChoosee;

	public TrizPlayer() {
		iterations = 0;
		maxChoose = Integer.MIN_VALUE;
		minChoose = Integer.MAX_VALUE;
		maxChoosee = Integer.MIN_VALUE;
		minChoosee = Integer.MAX_VALUE;
	}

	@Override
	public void setPointSystem(PokerSquaresPointSystem system, long millis) {
		// If it's random, we might actually WANT to be wasting time going for
		// every royal flush!
		if (system != PokerSquaresPointSystem.getAmericanPointSystem()
				&& system != PokerSquaresPointSystem.getBritishPointSystem()
				&& system != PokerSquaresPointSystem.getAmeritishPointSystem()) {
			RF_DIRTY_HARRY = 0;
		}
		this.millis = millis;
		highCardScore = system.getScoreTable()[0];
		this.system = system;
	}

	@Override
	public void init() {
		cardsInPlay = 0;
		plays.clear();
		for (int i = 0; i < 25; i++)
			plays.push(i);
		Collections.shuffle(plays);
		simDeck = new ArrayList<Card>(Arrays.asList(deck));
	}

	public int ChooseMoveFromChoices(Stack<Integer> choices, Card c,
			long allotedTime) {
		int bestMove = -1;
		double highestScore = -50000;
		Card[][] simGrid = new Card[SIZE][SIZE];
		ArrayList<Card> deckCopy;
		long millisPer = allotedTime / choices.size();
		while (!choices.isEmpty()) {
			int move = choices.pop();
			this.GreedyResult = 0;
			Stack<Integer> movesLeft = new Stack<Integer>();
			for (int i = 0; i < move; i++) {
				simGrid[i / 5][i % 5] = this.grid[i / 5][i % 5];
				if (simGrid[i / 5][i % 5] == null) {
					movesLeft.push(i);
				}
			}
			simGrid[move / 5][move % 5] = c;
			for (int i = move + 1; i < SIZE * SIZE; i++) {
				simGrid[i / 5][i % 5] = this.grid[i / 5][i % 5];
				if (simGrid[i / 5][i % 5] == null) {
					movesLeft.push(i);
				}
			}

			Stack<Integer> mlCopy = new Stack<Integer>();
			this.startMillis = System.currentTimeMillis();
			int totalSims = 0;
			int[] potentials = new int[2 * SIZE];
			while (System.currentTimeMillis() - this.startMillis < millisPer) {
				iterations++;
				totalSims++;
				deckCopy = new ArrayList<Card>(simDeck);
				mlCopy.addAll(movesLeft);
				Collections.shuffle(deckCopy);
				this.SimulateGreedyMove(potentials, 0, simGrid, deckCopy,
						mlCopy);
			}

			// System.out.println("Round " + cardsDrawn + " got " + totalSims +
			// " iterations");
			if (this.GreedyResult / totalSims > highestScore) {
				highestScore = this.GreedyResult / totalSims;
				bestMove = move;
			}
			// System.out.println("My average was: " + this.GreedyResult /
			// totalSims);
			simGrid[move / 5][move % 5] = null;
		}
		return bestMove;
	}

	public double getPotentialChange(Card[][] grid, Card c, int move,
			ArrayList<Card> deck) {
		Card[] row = grid[move / 5];
		Card[] column = new Card[SIZE];
		for (int i = 0; i < SIZE; i++) {
			column[i] = grid[i][move % 5];
		}
		// double oldColumn = getPotential(column, deck);
		// double oldRow = getPotential(row, deck);
		column[move / 5] = c;
		row[move % 5] = c;
		double newColumn = getPotential(column, deck);
		double newRow = getPotential(row, deck);
		grid[move / 5][move % 5] = null;
		return (newColumn + newRow);// - (oldColumn + oldRow);
	}

	public double getPotential(Card[] hand, ArrayList<Card> deck) {
		InfoBomb ib = new InfoBomb(hand, deck);
		int[] table = system.getScoreTable();
		boolean[] potentials = new boolean[10];
		potentials[0] = true;
		potentials[1] = (ib.size <= 4) || (ib.numDuplicates == 1);// pairPotential(ib);
		potentials[2] = twoPairPotential(ib);
		potentials[3] = threePotential(ib);
		potentials[4] = straightPotential(ib);
		potentials[5] = ib.evenSuit;
		potentials[6] = fhPotential(ib);
		potentials[7] = fourPotential(ib);
		potentials[8] = false;
		potentials[9] = false;

		if (potentials[4] && potentials[5]) {
			potentials[8] = true;
			// System.out.println("Calling rf potential");
			potentials[9] = rfPotential(ib);
		}
		double maxPotential = -10000;
		for (int i = 0; i < 10; i++) {
			if (potentials[i]) {
				maxPotential = Math.max(maxPotential, table[i]);
			}
		}
		// System.out.println(maxPotential + " " + ib.percent);
		return maxPotential * ib.percent;
	}

	public boolean twoPairPotential(InfoBomb ib) {
		if (ib.size <= 3) {
			return true;
		} else if (ib.size == 4 && ib.numDuplicates > 0) {
			return true;
		} else {
			return (ib.numDuplicates == 2 && ib.triples == false);
		}
	}

	public boolean threePotential(InfoBomb ib) {
		if (ib.size <= 3) {
			return true;
		} else if (ib.size == 4 && (ib.numDuplicates == 1)) { // note that we
																// only allow
																// one pair - if
																// we have two
																// pairs, we
																// don't have
																// three
																// potential, we
																// have FH
																// potential as
																// recognized by
																// game.
			return true;
		} else {
			return ib.triples;
		}
	}

	public boolean fourPotential(InfoBomb ib) {
		if (ib.size <= 2) {
			return true;
		} else if (ib.size == 3 && (ib.triples || ib.duplicates)) {
			return true;
		} else if (ib.size == 4 && (ib.triples || ib.quads)) {
			return true;
		} else {
			return ib.quads;
		}
	}

	public boolean rfPotential(InfoBomb ib) {

		if ((ib.maxRank == 0 || (ib.maxRank <= 12 && ib.maxRank >= 8))
				&& (ib.minRank == 0 || ib.minRank >= 8)) {

			return RfPlausible(ib);
		}
		// System.out.println("- NO RF");
		return false;
	}

	public double Choose(int a, int b) {
		if (b == 1) {
			return a;
		}
		String k = "" + a + "," + b;

		double product = 1;
		int count1 = 1;
		int count2 = 1;
		int count3 = 1;
		int flag = 0;
		while (flag != 3) {
			flag = 0;
			if (count1 <= a) {
				product *= count1;
				count1++;
			} else {
				flag++;
			}
			if (count2 <= b) {
				product = product / count2;
				count2++;
			} else {
				flag++;
			}
			if (count3 <= (a - b)) {
				product = product / count3;
				count3++;
			} else {
				flag++;
			}
		}
		return Math.floor(product * 100) / 100;

	}

	public boolean RfPlausible(InfoBomb ib) {
		int cardsNeeded = SIZE - ib.size;
		int cardsInDeck = ib.deck.size();
		int cardsInPlay = 52 - ib.deck.size();
		int cardsLeftToPlay = 25 - cardsInPlay;
		double product = Choose(cardsInDeck, (cardsLeftToPlay - cardsNeeded))
				/ Choose(cardsInDeck, cardsLeftToPlay);

		if (product < RF_DIRTY_HARRY) {
			return false;
		}
		return true;
	}

	public boolean fhPotential(InfoBomb ib) {
		if (ib.size == 1) {
			return true;
		}
		if (ib.amts.size() > 2) {
			// System.out.println("No FH potential");
			return false;
		}
		if (ib.quads) {
			return false;
		}
		// System.out.println("Has FH potential!!");
		return true;
	}

	public boolean straightPotential(InfoBomb ib) {
		if (ib.size == 1) {
			return true;
		}
		if (ib.duplicates) {
			return false;
		}
		if (ib.maxRank - ib.minRank <= 4) {
			// System.out.println("Straight potential!");
			return true;
		}
		// System.out.println("No straight potential: too big a spread");
		return false;
	}

	public double OneCardPotential(Card c) {
		int maxPotential = -10000000;
		int[] table = system.getScoreTable();
		for (int i = 0; i < 9; i++) {
			if ((i < 9) && (table[i] > maxPotential)) {
				maxPotential = table[i];
			}
		}
		if (c.getRank() >= 8 || c.getRank() == 0) {
			if (table[9] > maxPotential) {
				maxPotential = table[9];
			}
		}
		return maxPotential;
	}

	public void SimulateGreedyMove(int[] ps, double currentScore,
			Card[][] simGrid, ArrayList<Card> simDeck, Stack<Integer> moves) {
		// greedy greedy
		Stack<Integer> temp = new Stack<Integer>();
		int bestMove = -1;
		double highScore = -50000;
		Card lastCard = simDeck.get(simDeck.size() - 1);
		Stack<Integer> goodMoves = this.getMoveChoicesInSim(
				(Stack<Integer>) moves.clone(), simGrid);
		// system.printGrid(simGrid);
		// System.out.println("Initial size: " + moves.size());
		// System.out.println("Move size: " + goodMoves.size());
		double immediateScore = 0;
		double potentialScore = 0;
		while (!goodMoves.isEmpty()) {
			int move = goodMoves.pop();
			if (GetPlayType(move / 5, move % 5, simGrid) == 1) {
				immediateScore = highCardScore;
				// potentialScore = OneCardPotential(lastCard);
			} else {
				simGrid[move / 5][move % 5] = lastCard;
				immediateScore = system.getScore(simGrid);
			}
			potentialScore = this.getPotentialChange(simGrid, lastCard, move,
					simDeck);
			if (highScore < (POTENTIAL_WEIGHT * potentialScore)
					+ ((1 - POTENTIAL_WEIGHT) * immediateScore)) {
				bestMove = move;
				highScore = (POTENTIAL_WEIGHT * potentialScore)
						+ ((1 - POTENTIAL_WEIGHT) * immediateScore);
			}
			simGrid[move / 5][move % 5] = null;
		}

		simGrid[bestMove / 5][bestMove % 5] = lastCard;
		simDeck.remove(simDeck.size() - 1);
		int m;
		while (!moves.isEmpty()) {
			if ((m = moves.pop()) != bestMove) {
				temp.push(m);
			}
		}
		if (simDeck.size() == 27) {

			// System.out.println("My score is: " + highScore);
			this.GreedyResult += system.getScore(simGrid);
			return;
		}
		SimulateGreedyMove(ps, highScore, simGrid, simDeck, temp);
	}

	@Override
	public int[] getPlay(Card card, long millisRemaining) {
		simDeck.remove(card);
		if (cardsInPlay == 24) {
			System.out.println(iterations);
		}
		// If it's our first or last move, we can just randomize it
		if (cardsInPlay == 0 || cardsInPlay == 24) {
			int play = plays.pop();
			int[] playPos = { play / 5, play % 5 };
			this.grid[play / 5][play % 5] = card;
			cardsInPlay++;
			return playPos;
		}
		// Get all plausible moves and choose the best play of all of them
		Stack<Integer> moveChoices = this.getMoveChoices(
				(Stack<Integer>) plays.clone(), this.grid);

		int bestPlay = this.ChooseMoveFromChoices(moveChoices, card,
				((this.millis / 23) - 50));
		// Slinky swap the stacks and remove the best play from the remaining
		// moves
		while (!plays.isEmpty()) {
			int tempPlay = plays.pop();
			if (tempPlay != bestPlay) {
				temp.push(tempPlay);
			}
		}
		while (!temp.isEmpty()) {
			plays.push(temp.pop());
		}
		// Make the return value and return it!
		int[] playPos = { bestPlay / 5, bestPlay % 5 }; // decode it into row
														// and column
		this.grid[bestPlay / 5][bestPlay % 5] = card;
		cardsInPlay++;
		return playPos; // return it
	}

	public Stack<Integer> getMoveChoicesInSim(Stack<Integer> plays, Card[][] g) {
		boolean[] rowTypeTwo = new boolean[SIZE];
		boolean[] columnTypeTwo = new boolean[SIZE];
		Stack<Integer> choices = new Stack<Integer>();
		boolean typeOneSaved = false;
		while (!plays.isEmpty()) {
			int p = plays.pop();
			int type = this.GetPlayType(p / 5, p % 5, g);
			if (type == 1 && !typeOneSaved) {
				typeOneSaved = true;
				choices.push(p);
			} else if (type == 2) {
				if (rowTypeTwo[p / 5] || columnTypeTwo[p % 5]) {
				} else {
					if (this.IsRowTT(p, grid)) {
						rowTypeTwo[p / 5] = true;
					} else {
						columnTypeTwo[p % 5] = true;
					}
					choices.push(p);
				}
			} else {
				choices.push(p);
			}
		}
		return choices;
	}

	public Stack<Integer> getMoveChoices(Stack<Integer> plays, Card[][] grid) {
		/*
		 * When we're choosing where to put cards, we have a few types of
		 * choices we can make as to the location: 1) Put it in empty column and
		 * empty row - we only need one of these options since they don't matter
		 * at all 2) Put it in an empty row/column and taken column/row - we
		 * only need one of these for a given column or row 3) Put it in an
		 * occupied column AND row. Very specific, keep every instance of this
		 * that we can
		 */
		// int onecount = 0;
		// int twocount = 0;
		// int threecount = 0;
		ArrayList<Integer> forbiddens = new ArrayList<Integer>();
		boolean typeOneSaved = false;
		Stack<Integer> choices = new Stack<Integer>();
		boolean[] rowTypeTwo = new boolean[SIZE];
		boolean[] columnTypeTwo = new boolean[SIZE];
		while (!plays.isEmpty()) {
			int play = plays.pop();
			int type = this.GetPlayType(play / 5, play % 5, grid);
			if (type == 1 && !typeOneSaved) {
				typeOneSaved = true;
				// onecount++;
				choices.push(play);
			} else if (type == 3) {
				int row = play / 5;
				int column = play % 5;
				int res;
				boolean flag = true;
				if ((res = isOneAndOne(row, column, grid)) != -1) {
					forbiddens.add(res);
					for (int i = 0; i < forbiddens.size(); i++) {
						if (play == forbiddens.get(i)) {
							flag = false;
						}
					}
					if (flag) {
						// threecount++;
						choices.push(play);
					}
				} else {
					// threecount++;
					choices.push(play);
				}
			} else if (type == 2) {
				if (rowTypeTwo[play / 5] || columnTypeTwo[play % 5]) {
				} else {
					if (this.IsRowTT(play, grid)) {
						rowTypeTwo[play / 5] = true;
					} else {
						columnTypeTwo[play % 5] = true;
					}
					// twocount++;
					choices.push(play);
				}
			}
		}
		/*
		 * System.out.println("There are this many choices: " + choices.size());
		 * System.out.println("1: " + onecount); System.out.println("2: " +
		 * twocount); System.out.println("3: " + threecount);
		 */
		return choices;
	}

	public int isOneAndOne(int row, int column, Card[][] g) {
		int rowCount = 0;
		int columnCount = 0;
		int r = 0;
		int c = 0;
		for (int i = 0; i < 5; i++) {
			// through columns
			if (g[row][i] != null) {
				rowCount++;
				c = i;
			}
			// through rows
			if (g[i][column] != null) {
				columnCount++;
				r = i;
			}
		}
		if (rowCount == 0 || columnCount == 0) {
			System.err.println("YOU DONE MESSED UP");
		}
		if (rowCount == 1 && columnCount == 1) {

			return (r * 5) + c;
		}
		return -1;
	}

	public boolean IsRowTT(int play, Card[][] g) {
		for (int i = 0; i < SIZE; i++) {
			if (g[play / 5][i] != null) {
				return true;
			}
		}
		return false;
	}

	public int GetPlayType(int r, int c, Card[][] grid) {
		int rowOccupied = 0;
		int columnOccupied = 0;
		for (int i = 0; i < SIZE; i++) {
			if (grid[i][c] != null) {
				columnOccupied = 1;
			}
			if (grid[r][i] != null) {
				rowOccupied = 1;
			}
		}
		return rowOccupied + columnOccupied + 1; // we add the one to give us
													// either type 1, 2, or 3
													// instead of 0, 1, 2
	}

	@Override
	public String getName() {
		return "JoTriz";
	}

	public static void main(String[] args) {
		PokerSquaresPointSystem system = PokerSquaresPointSystem
				.getAmericanPointSystem();
		System.out.println(system);
		int nTrials = 1;
		long totalTime = 0;
		int totalScore = 0;
		int wins = 0;
		long maxTime = Long.MIN_VALUE;
		long minTime = Long.MAX_VALUE;
		int maxScore = Integer.MIN_VALUE;
		int minScore = Integer.MAX_VALUE;
		for (int i = 0; i < nTrials; i++) {
			long startTime = System.currentTimeMillis();
			int score = new PokerSquares(new TrizPlayer(), system).play(); // play
																		// a
																		// single
																		// game
			long endTime = System.currentTimeMillis();
			System.out.println("Game " + i + " earned " + score
					+ " points and took " + (endTime - startTime) + " ms.");
			long elapsed = endTime - startTime;
			totalTime += elapsed;
			if (elapsed > maxTime) {
				maxTime = elapsed;
			}
			if (elapsed < minTime) {
				minTime = elapsed;
			}
			totalScore += score;
			if (score > maxScore) {
				maxScore = score;
			}
			if (score < minScore) {
				minScore = score;
			}
			if (score > 200) {
				wins++;
			}
		}
		System.out
				.println(nTrials + " trials were run with " + wins + " wins.");
		System.out
				.println("---------------------------------------------------------------------");
		System.out.println("The average time was: " + (totalTime / nTrials)
				+ " milliseconds");
		System.out.println("The max time was: " + maxTime
				+ " and the min time was: " + minTime);
		System.out.println("The average score was: " + (totalScore / nTrials));
		System.out.println("The max score was : " + maxScore
				+ " and the min score was: " + minScore);
	}


}
