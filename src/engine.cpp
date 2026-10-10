#include <algorithm>
#include <array>
#include <atomic>
#include <cassert>
#include <chrono>
#include <cctype>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <iomanip>
#include <iostream>
#include <limits>
#include <mutex>
#include <sstream>
#include <string>
#include <thread>
#include <vector>
#if defined(_MSC_VER)
#include <intrin.h>
#endif

namespace {

using U64 = std::uint64_t;
using Clock = std::chrono::steady_clock;

constexpr int WHITE = 0;
constexpr int BLACK = 1;
constexpr int PAWN = 0;
constexpr int KNIGHT = 1;
constexpr int BISHOP = 2;
constexpr int ROOK = 3;
constexpr int QUEEN = 4;
constexpr int KING = 5;
constexpr int NO_PIECE = 0;
constexpr int MAX_PLY = 128;
constexpr int INF = 32000;
constexpr int MATE = 30000;
constexpr int MATE_THRESHOLD = MATE - MAX_PLY;
constexpr int WK_CASTLE = 1;
constexpr int WQ_CASTLE = 2;
constexpr int BK_CASTLE = 4;
constexpr int BQ_CASTLE = 8;
constexpr const char* START_FEN = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";

std::array<U64, 64> knightAttacks{};
std::array<U64, 64> kingAttacks{};
std::array<std::array<U64, 64>, 2> pawnAttacks{};
std::array<std::array<U64, 64>, 13> zobristPiece{};
std::array<U64, 16> zobristCastle{};
std::array<U64, 64> zobristEp{};
U64 zobristSide = 0;
bool tablesInitialized = false;

inline U64 bit(int sq) { return U64{1} << sq; }
inline int file_of(int sq) { return sq & 7; }
inline int rank_of(int sq) { return sq >> 3; }
inline int piece_color(int piece) { return (piece - 1) / 6; }
inline int piece_type(int piece) { return (piece - 1) % 6; }
inline int make_piece(int color, int type) { return 1 + color * 6 + type; }
inline int popcount(U64 b) {
#if defined(_MSC_VER)
    return static_cast<int>(__popcnt64(b));
#else
    return __builtin_popcountll(b);
#endif
}

int pop_lsb(U64& b) {
#if defined(_MSC_VER)
    unsigned long index = 0;
    _BitScanForward64(&index, b);
    const int sq = static_cast<int>(index);
#else
    const int sq = __builtin_ctzll(b);
#endif
    b &= b - 1;
    return sq;
}

U64 splitmix64(U64& state) {
    U64 z = (state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

void init_tables() {
    if (tablesInitialized) return;

    constexpr int knightSteps[8][2] = {
        {1, 2}, {2, 1}, {2, -1}, {1, -2},
        {-1, -2}, {-2, -1}, {-2, 1}, {-1, 2}
    };
    constexpr int kingSteps[8][2] = {
        {1, 0}, {1, 1}, {0, 1}, {-1, 1},
        {-1, 0}, {-1, -1}, {0, -1}, {1, -1}
    };

    for (int sq = 0; sq < 64; ++sq) {
        const int f = file_of(sq);
        const int r = rank_of(sq);
        for (const auto& d : knightSteps) {
            const int nf = f + d[0];
            const int nr = r + d[1];
            if (nf >= 0 && nf < 8 && nr >= 0 && nr < 8)
                knightAttacks[sq] |= bit(nr * 8 + nf);
        }
        for (const auto& d : kingSteps) {
            const int nf = f + d[0];
            const int nr = r + d[1];
            if (nf >= 0 && nf < 8 && nr >= 0 && nr < 8)
                kingAttacks[sq] |= bit(nr * 8 + nf);
        }
        for (int df : {-1, 1}) {
            if (f + df >= 0 && f + df < 8) {
                if (r + 1 < 8) pawnAttacks[WHITE][sq] |= bit((r + 1) * 8 + f + df);
                if (r - 1 >= 0) pawnAttacks[BLACK][sq] |= bit((r - 1) * 8 + f + df);
            }
        }
    }

    U64 seed = 0x6d697472615f3236ULL;
    for (int p = 1; p <= 12; ++p)
        for (int sq = 0; sq < 64; ++sq)
            zobristPiece[p][sq] = splitmix64(seed);
    for (U64& x : zobristCastle) x = splitmix64(seed);
    for (U64& x : zobristEp) x = splitmix64(seed);
    zobristSide = splitmix64(seed);
    tablesInitialized = true;
}

U64 sliding_attacks(int sq, U64 occupied, bool diagonal) {
    constexpr int rookDirs[4][2] = {{1, 0}, {-1, 0}, {0, 1}, {0, -1}};
    constexpr int bishopDirs[4][2] = {{1, 1}, {1, -1}, {-1, 1}, {-1, -1}};
    const int (*dirs)[2] = diagonal ? bishopDirs : rookDirs;
    U64 attacks = 0;
    const int f = file_of(sq);
    const int r = rank_of(sq);
    for (int d = 0; d < 4; ++d) {
        int nf = f + dirs[d][0];
        int nr = r + dirs[d][1];
        while (nf >= 0 && nf < 8 && nr >= 0 && nr < 8) {
            const int to = nr * 8 + nf;
            attacks |= bit(to);
            if (occupied & bit(to)) break;
            nf += dirs[d][0];
            nr += dirs[d][1];
        }
    }
    return attacks;
}

inline U64 rook_attacks(int sq, U64 occupied) { return sliding_attacks(sq, occupied, false); }
inline U64 bishop_attacks(int sq, U64 occupied) { return sliding_attacks(sq, occupied, true); }

struct Move {
    std::uint8_t from = 0;
    std::uint8_t to = 0;
    // 0 means no promotion; otherwise use the piece type (KNIGHT..QUEEN).
    std::uint8_t promotion = 0;

    std::uint32_t code() const {
        return std::uint32_t(from) | (std::uint32_t(to) << 6) |
               (std::uint32_t(promotion) << 12);
    }
    static Move from_code(std::uint32_t c) {
        return Move{static_cast<std::uint8_t>(c & 63),
                    static_cast<std::uint8_t>((c >> 6) & 63),
                    static_cast<std::uint8_t>((c >> 12) & 7)};
    }
    bool operator==(const Move& other) const {
        return from == other.from && to == other.to && promotion == other.promotion;
    }
    bool operator!=(const Move& other) const { return !(*this == other); }
    explicit operator bool() const { return code() != 0; }
};

struct MoveList {
    std::array<Move, 256> moves{};
    int size = 0;
    void push(Move m) {
        assert(size < static_cast<int>(moves.size()));
        moves[size++] = m;
    }
    Move& operator[](int i) { return moves[i]; }
    const Move& operator[](int i) const { return moves[i]; }
};

struct Undo {
    U64 key = 0;
    int side = WHITE;
    int castling = 0;
    int ep = -1;
    int halfmove = 0;
    int fullmove = 1;
    int capturedSquare = -1;
    int captured = NO_PIECE;
    int moving = NO_PIECE;
};

struct NullUndo {
    U64 key = 0;
    int side = WHITE;
    int ep = -1;
    int halfmove = 0;
    int nullDepth = 0;
};

struct Position {
    std::array<int, 64> board{};
    std::array<std::array<U64, 6>, 2> pieces{};
    std::array<U64, 2> occupied{};
    U64 all = 0;
    int side = WHITE;
    int castling = 0;
    int ep = -1;
    int halfmove = 0;
    int fullmove = 1;
    int nullDepth = 0;
    U64 key = 0;
    std::vector<U64> keyHistory;

    void clear() {
        board.fill(NO_PIECE);
        for (auto& c : pieces) c.fill(0);
        occupied.fill(0);
        all = 0;
        side = WHITE;
        castling = 0;
        ep = -1;
        halfmove = 0;
        fullmove = 1;
        nullDepth = 0;
        key = 0;
        keyHistory.clear();
    }

    void add_piece(int p, int sq) {
        assert(p != NO_PIECE && board[sq] == NO_PIECE);
        board[sq] = p;
        const int c = piece_color(p);
        const int t = piece_type(p);
        pieces[c][t] |= bit(sq);
        occupied[c] |= bit(sq);
        all |= bit(sq);
        key ^= zobristPiece[p][sq];
    }

    int remove_piece(int sq) {
        const int p = board[sq];
        if (p == NO_PIECE) return NO_PIECE;
        const int c = piece_color(p);
        const int t = piece_type(p);
        board[sq] = NO_PIECE;
        pieces[c][t] &= ~bit(sq);
        occupied[c] &= ~bit(sq);
        all &= ~bit(sq);
        key ^= zobristPiece[p][sq];
        return p;
    }

    U64 recompute_key() const {
        U64 h = 0;
        for (int sq = 0; sq < 64; ++sq)
            if (board[sq] != NO_PIECE) h ^= zobristPiece[board[sq]][sq];
        h ^= zobristCastle[castling];
        if (ep >= 0) h ^= zobristEp[ep];
        if (side == BLACK) h ^= zobristSide;
        return h;
    }

    int king_square(int color) const {
        U64 b = pieces[color][KING];
        return b ? pop_lsb(b) : -1;
    }

    bool square_attacked(int sq, int byColor, U64 occupiedOverride) const {
        if (sq < 0 || sq >= 64) return false;
        if (pawnAttacks[byColor ^ 1][sq] & pieces[byColor][PAWN]) return true;
        if (knightAttacks[sq] & pieces[byColor][KNIGHT]) return true;
        if (kingAttacks[sq] & pieces[byColor][KING]) return true;
        if (rook_attacks(sq, occupiedOverride) &
            (pieces[byColor][ROOK] | pieces[byColor][QUEEN])) return true;
        if (bishop_attacks(sq, occupiedOverride) &
            (pieces[byColor][BISHOP] | pieces[byColor][QUEEN])) return true;
        return false;
    }

    bool square_attacked(int sq, int byColor) const { return square_attacked(sq, byColor, all); }

    bool in_check(int color) const {
        const int k = king_square(color);
        return k >= 0 && square_attacked(k, color ^ 1);
    }

    bool insufficient_material() const {
        if (pieces[WHITE][PAWN] || pieces[BLACK][PAWN] ||
            pieces[WHITE][ROOK] || pieces[BLACK][ROOK] ||
            pieces[WHITE][QUEEN] || pieces[BLACK][QUEEN]) return false;
        const int minors = popcount(pieces[WHITE][KNIGHT] | pieces[WHITE][BISHOP] |
                                    pieces[BLACK][KNIGHT] | pieces[BLACK][BISHOP]);
        return minors <= 1;
    }

    bool repetition(int rootHistoryIndex) const {
        if (nullDepth > 0 || keyHistory.size() < 3) return false;
        const int current = static_cast<int>(keyHistory.size()) - 1;
        const int lower = std::max(0, current - halfmove);
        int priorMatches = 0;
        for (int i = current - 2; i >= lower; i -= 2) {
            if (keyHistory[static_cast<std::size_t>(i)] == key) {
                // A cycle created within this search can be scored as a draw immediately.
                if (i >= rootHistoryIndex) return true;
                if (++priorMatches >= 2) return true; // threefold in the played game
            }
        }
        return false;
    }

    void make_move(Move m, Undo& u) {
        u.key = key;
        u.side = side;
        u.castling = castling;
        u.ep = ep;
        u.halfmove = halfmove;
        u.fullmove = fullmove;
        u.moving = board[m.from];
        u.capturedSquare = m.to;
        u.captured = board[m.to];
        const int us = side;
        const int type = piece_type(u.moving);

        if (type == PAWN && m.to == ep && board[m.to] == NO_PIECE &&
            file_of(m.from) != file_of(m.to)) {
            u.capturedSquare = m.to + (us == WHITE ? -8 : 8);
            u.captured = board[u.capturedSquare];
        }

        if (ep >= 0) key ^= zobristEp[ep];
        key ^= zobristCastle[castling];

        remove_piece(m.from);
        if (u.captured != NO_PIECE) remove_piece(u.capturedSquare);

        if (type == KING && std::abs(file_of(m.to) - file_of(m.from)) == 2) {
            const int rankBase = us == WHITE ? 0 : 56;
            if (file_of(m.to) == 6) {
                remove_piece(rankBase + 7);
                add_piece(make_piece(us, ROOK), rankBase + 5);
            } else {
                remove_piece(rankBase);
                add_piece(make_piece(us, ROOK), rankBase + 3);
            }
        }

        if (m.promotion) add_piece(make_piece(us, m.promotion), m.to);
        else add_piece(u.moving, m.to);

        if (type == KING) {
            castling &= us == WHITE ? ~(WK_CASTLE | WQ_CASTLE) : ~(BK_CASTLE | BQ_CASTLE);
        }
        if (type == ROOK) {
            if (m.from == 0) castling &= ~WQ_CASTLE;
            if (m.from == 7) castling &= ~WK_CASTLE;
            if (m.from == 56) castling &= ~BQ_CASTLE;
            if (m.from == 63) castling &= ~BK_CASTLE;
        }
        if (u.captured != NO_PIECE && piece_type(u.captured) == ROOK) {
            if (u.capturedSquare == 0) castling &= ~WQ_CASTLE;
            if (u.capturedSquare == 7) castling &= ~WK_CASTLE;
            if (u.capturedSquare == 56) castling &= ~BQ_CASTLE;
            if (u.capturedSquare == 63) castling &= ~BK_CASTLE;
        }

        ep = -1;
        if (type == PAWN && std::abs(m.to - m.from) == 16) ep = (m.to + m.from) / 2;
        halfmove = (type == PAWN || u.captured != NO_PIECE) ? 0 : halfmove + 1;
        if (us == BLACK) ++fullmove;
        side ^= 1;

        key ^= zobristSide;
        key ^= zobristCastle[castling];
        if (ep >= 0) key ^= zobristEp[ep];
        keyHistory.push_back(key);
    }

    void undo_move(Move m, const Undo& u) {
        if (!keyHistory.empty()) keyHistory.pop_back();
        const int us = u.side;
        remove_piece(m.to);

        if (piece_type(u.moving) == KING && std::abs(file_of(m.to) - file_of(m.from)) == 2) {
            const int rankBase = us == WHITE ? 0 : 56;
            if (file_of(m.to) == 6) {
                remove_piece(rankBase + 5);
                add_piece(make_piece(us, ROOK), rankBase + 7);
            } else {
                remove_piece(rankBase + 3);
                add_piece(make_piece(us, ROOK), rankBase);
            }
        }

        add_piece(u.moving, m.from);
        if (u.captured != NO_PIECE) add_piece(u.captured, u.capturedSquare);
        side = u.side;
        castling = u.castling;
        ep = u.ep;
        halfmove = u.halfmove;
        fullmove = u.fullmove;
        key = u.key;
    }

    void make_null(NullUndo& u) {
        u.key = key;
        u.side = side;
        u.ep = ep;
        u.halfmove = halfmove;
        u.nullDepth = nullDepth;
        if (ep >= 0) key ^= zobristEp[ep];
        ep = -1;
        side ^= 1;
        key ^= zobristSide;
        ++nullDepth;
    }

    void undo_null(const NullUndo& u) {
        key = u.key;
        side = u.side;
        ep = u.ep;
        halfmove = u.halfmove;
        nullDepth = u.nullDepth;
    }
};

int char_to_piece(char c) {
    switch (c) {
        case 'P': return make_piece(WHITE, PAWN);
        case 'N': return make_piece(WHITE, KNIGHT);
        case 'B': return make_piece(WHITE, BISHOP);
        case 'R': return make_piece(WHITE, ROOK);
        case 'Q': return make_piece(WHITE, QUEEN);
        case 'K': return make_piece(WHITE, KING);
        case 'p': return make_piece(BLACK, PAWN);
        case 'n': return make_piece(BLACK, KNIGHT);
        case 'b': return make_piece(BLACK, BISHOP);
        case 'r': return make_piece(BLACK, ROOK);
        case 'q': return make_piece(BLACK, QUEEN);
        case 'k': return make_piece(BLACK, KING);
        default: return NO_PIECE;
    }
}

bool parse_square(const std::string& s, int& sq) {
    if (s.size() != 2 || s[0] < 'a' || s[0] > 'h' || s[1] < '1' || s[1] > '8') return false;
    sq = (s[1] - '1') * 8 + (s[0] - 'a');
    return true;
}

std::string square_name(int sq) {
    if (sq < 0 || sq >= 64) return "--";
    std::string s = "a1";
    s[0] = static_cast<char>('a' + file_of(sq));
    s[1] = static_cast<char>('1' + rank_of(sq));
    return s;
}

bool parse_fen(const std::string& fen, Position& p, std::string* error = nullptr) {
    p.clear();
    std::istringstream in(fen);
    std::string placement, stm, rights, epText;
    if (!(in >> placement >> stm >> rights >> epText)) {
        if (error) *error = "FEN must contain at least four fields";
        return false;
    }
    in >> p.halfmove >> p.fullmove;
    if (p.fullmove <= 0) p.fullmove = 1;
    if (p.halfmove < 0) p.halfmove = 0;

    int rank = 7;
    int file = 0;
    for (char c : placement) {
        if (c == '/') {
            if (file != 8 || rank == 0) {
                if (error) *error = "Malformed FEN board layout";
                return false;
            }
            --rank;
            file = 0;
        } else if (c >= '1' && c <= '8') {
            file += c - '0';
            if (file > 8) {
                if (error) *error = "Malformed FEN rank width";
                return false;
            }
        } else {
            const int piece = char_to_piece(c);
            if (!piece || file >= 8 || rank < 0) {
                if (error) *error = "Malformed FEN piece placement";
                return false;
            }
            p.add_piece(piece, rank * 8 + file);
            ++file;
        }
    }
    if (rank != 0 || file != 8) {
        if (error) *error = "FEN board must contain eight complete ranks";
        return false;
    }

    if (stm == "w") p.side = WHITE;
    else if (stm == "b") p.side = BLACK;
    else {
        if (error) *error = "FEN active color must be w or b";
        return false;
    }

    p.castling = 0;
    if (rights != "-") {
        for (char c : rights) {
            switch (c) {
                case 'K': p.castling |= WK_CASTLE; break;
                case 'Q': p.castling |= WQ_CASTLE; break;
                case 'k': p.castling |= BK_CASTLE; break;
                case 'q': p.castling |= BQ_CASTLE; break;
                default:
                    if (error) *error = "Malformed FEN castling rights";
                    return false;
            }
        }
    }

    p.ep = -1;
    if (epText != "-" && !parse_square(epText, p.ep)) {
        if (error) *error = "Malformed FEN en-passant square";
        return false;
    }
    p.key = p.recompute_key();
    p.keyHistory.push_back(p.key);
    return true;
}

bool can_castle(const Position& p, int color, bool kingSide) {
    const int right = color == WHITE ? (kingSide ? WK_CASTLE : WQ_CASTLE)
                                     : (kingSide ? BK_CASTLE : BQ_CASTLE);
    if (!(p.castling & right)) return false;
    const int base = color == WHITE ? 0 : 56;
    const int kingFrom = base + 4;
    const int rookFrom = base + (kingSide ? 7 : 0);
    if (p.board[kingFrom] != make_piece(color, KING) ||
        p.board[rookFrom] != make_piece(color, ROOK)) return false;

    const int emptyStart = kingSide ? base + 5 : base + 1;
    const int emptyEnd = kingSide ? base + 6 : base + 3;
    for (int sq = emptyStart; sq <= emptyEnd; ++sq)
        if (p.board[sq] != NO_PIECE) return false;

    const int enemy = color ^ 1;
    if (p.square_attacked(kingFrom, enemy)) return false;
    const U64 occWithoutKing = p.all & ~bit(kingFrom);
    const int transit = base + (kingSide ? 5 : 3);
    const int destination = base + (kingSide ? 6 : 2);
    if (p.square_attacked(transit, enemy, occWithoutKing)) return false;
    if (p.square_attacked(destination, enemy, occWithoutKing)) return false;
    return true;
}

void generate_pseudo(const Position& p, MoveList& list, bool capturesOnly = false) {
    list.size = 0;
    const int us = p.side;
    const int them = us ^ 1;
    const U64 own = p.occupied[us];
    const U64 enemy = p.occupied[them];

    U64 pawns = p.pieces[us][PAWN];
    while (pawns) {
        const int from = pop_lsb(pawns);
        const int r = rank_of(from);
        const int step = us == WHITE ? 8 : -8;
        const int promotionRank = us == WHITE ? 6 : 1;
        const int startRank = us == WHITE ? 1 : 6;
        const int next = from + step;

        if (next >= 0 && next < 64 && p.board[next] == NO_PIECE &&
            (!capturesOnly || r == promotionRank)) {
            if (r == promotionRank) {
                list.push(Move{static_cast<std::uint8_t>(from), static_cast<std::uint8_t>(next), QUEEN});
                list.push(Move{static_cast<std::uint8_t>(from), static_cast<std::uint8_t>(next), ROOK});
                list.push(Move{static_cast<std::uint8_t>(from), static_cast<std::uint8_t>(next), BISHOP});
                list.push(Move{static_cast<std::uint8_t>(from), static_cast<std::uint8_t>(next), KNIGHT});
            } else if (!capturesOnly) {
                list.push(Move{static_cast<std::uint8_t>(from), static_cast<std::uint8_t>(next), 0});
                const int twice = from + 2 * step;
                if (r == startRank && p.board[twice] == NO_PIECE)
                    list.push(Move{static_cast<std::uint8_t>(from), static_cast<std::uint8_t>(twice), 0});
            }
        }

        U64 captures = pawnAttacks[us][from] & enemy;
        while (captures) {
            const int to = pop_lsb(captures);
            if (piece_type(p.board[to]) == KING) continue;
            if (r == promotionRank) {
                list.push(Move{static_cast<std::uint8_t>(from), static_cast<std::uint8_t>(to), QUEEN});
                list.push(Move{static_cast<std::uint8_t>(from), static_cast<std::uint8_t>(to), ROOK});
                list.push(Move{static_cast<std::uint8_t>(from), static_cast<std::uint8_t>(to), BISHOP});
                list.push(Move{static_cast<std::uint8_t>(from), static_cast<std::uint8_t>(to), KNIGHT});
            } else {
                list.push(Move{static_cast<std::uint8_t>(from), static_cast<std::uint8_t>(to), 0});
            }
        }
        if (p.ep >= 0 && (pawnAttacks[us][from] & bit(p.ep)))
            list.push(Move{static_cast<std::uint8_t>(from), static_cast<std::uint8_t>(p.ep), 0});
    }

    for (int type = KNIGHT; type <= KING; ++type) {
        U64 men = p.pieces[us][type];
        while (men) {
            const int from = pop_lsb(men);
            U64 targets = 0;
            if (type == KNIGHT) targets = knightAttacks[from];
            else if (type == BISHOP) targets = bishop_attacks(from, p.all);
            else if (type == ROOK) targets = rook_attacks(from, p.all);
            else if (type == QUEEN) targets = bishop_attacks(from, p.all) | rook_attacks(from, p.all);
            else targets = kingAttacks[from];
            targets &= ~own;
            while (targets) {
                const int to = pop_lsb(targets);
                if ((enemy & bit(to)) && piece_type(p.board[to]) == KING) continue;
                if (capturesOnly && !(enemy & bit(to))) continue;
                list.push(Move{static_cast<std::uint8_t>(from), static_cast<std::uint8_t>(to), 0});
            }
            if (type == KING && !capturesOnly) {
                if (can_castle(p, us, true))
                    list.push(Move{static_cast<std::uint8_t>(from), static_cast<std::uint8_t>(from + 2), 0});
                if (can_castle(p, us, false))
                    list.push(Move{static_cast<std::uint8_t>(from), static_cast<std::uint8_t>(from - 2), 0});
            }
        }
    }
}

void generate_legal(Position& p, MoveList& legal, bool capturesOnly = false) {
    MoveList pseudo;
    generate_pseudo(p, pseudo, capturesOnly);
    legal.size = 0;
    const int us = p.side;
    for (int i = 0; i < pseudo.size; ++i) {
        const Move m = pseudo[i];
        Undo u;
        p.make_move(m, u);
        const int king = p.king_square(us);
        const bool valid = king >= 0 && !p.square_attacked(king, p.side);
        p.undo_move(m, u);
        if (valid) legal.push(m);
    }
}

std::string move_to_string(Move m) {
    std::string s = square_name(m.from) + square_name(m.to);
    if (m.promotion) {
        static constexpr char promo[] = {'?', 'n', 'b', 'r', 'q', '?'};
        s.push_back(promo[m.promotion]);
    }
    return s;
}

bool parse_uci_move(Position& p, const std::string& text, Move& result) {
    MoveList legal;
    generate_legal(p, legal);
    for (int i = 0; i < legal.size; ++i) {
        if (move_to_string(legal[i]) == text) {
            result = legal[i];
            return true;
        }
    }
    return false;
}

std::uint64_t perft(Position& p, int depth) {
    if (depth <= 0) return 1;
    MoveList moves;
    generate_legal(p, moves);
    if (depth == 1) return static_cast<std::uint64_t>(moves.size);
    std::uint64_t nodes = 0;
    for (int i = 0; i < moves.size; ++i) {
        Undo u;
        p.make_move(moves[i], u);
        nodes += perft(p, depth - 1);
        p.undo_move(moves[i], u);
    }
    return nodes;
}

int evaluate(const Position& p) {
    static constexpr int mgValue[6] = {100, 325, 335, 500, 975, 0};
    static constexpr int egValue[6] = {120, 310, 330, 520, 940, 0};
    static constexpr int phaseValue[6] = {0, 1, 1, 2, 4, 0};
    int mgScore = 0;
    int egScore = 0;
    int phase = 0;
    std::array<std::array<int, 8>, 2> pawnFileCounts{};

    for (int color = WHITE; color <= BLACK; ++color) {
        const int sign = color == WHITE ? 1 : -1;
        for (int type = PAWN; type <= KING; ++type) {
            U64 men = p.pieces[color][type];
            phase += popcount(men) * phaseValue[type];
            while (men) {
                const int sq = pop_lsb(men);
                const int f = file_of(sq);
                const int r = color == WHITE ? rank_of(sq) : 7 - rank_of(sq);
                const int center = (7 - std::abs(2 * f - 7)) + (7 - std::abs(2 * r - 7));
                int mgPst = 0;
                int egPst = 0;
                switch (type) {
                    case PAWN:
                        mgPst = r * 7 - std::abs(2 * f - 7);
                        egPst = r * 11 - std::abs(2 * f - 7);
                        ++pawnFileCounts[color][f];
                        break;
                    case KNIGHT:
                        mgPst = center * 5 - (r <= 1 ? 12 : 0);
                        egPst = center * 4;
                        break;
                    case BISHOP:
                        mgPst = center * 3;
                        egPst = center * 3;
                        break;
                    case ROOK:
                        mgPst = (r == 6 ? 14 : 0) + (r == 0 ? 0 : 2);
                        egPst = (r == 6 ? 18 : 0) + r;
                        break;
                    case QUEEN:
                        mgPst = center * 2;
                        egPst = center * 3;
                        break;
                    case KING:
                        mgPst = -center * 3;
                        egPst = center * 7;
                        break;
                }
                mgScore += sign * (mgValue[type] + mgPst);
                egScore += sign * (egValue[type] + egPst);
            }
        }
    }

    // Pawn structure and passed-pawn bonuses.
    static constexpr int passedBonus[8] = {0, 0, 8, 18, 32, 52, 82, 0};
    for (int color = WHITE; color <= BLACK; ++color) {
        const int sign = color == WHITE ? 1 : -1;
        const U64 ownPawns = p.pieces[color][PAWN];
        const U64 enemyPawns = p.pieces[color ^ 1][PAWN];
        for (int f = 0; f < 8; ++f) {
            if (pawnFileCounts[color][f] > 1) {
                const int penalty = 13 * (pawnFileCounts[color][f] - 1);
                mgScore -= sign * penalty;
                egScore -= sign * (penalty + 4);
            }
        }
        U64 pawns = ownPawns;
        while (pawns) {
            const int sq = pop_lsb(pawns);
            const int f = file_of(sq);
            const int r = rank_of(sq);
            const int relativeRank = color == WHITE ? r : 7 - r;
            const bool hasNeighborFile = (f > 0 && pawnFileCounts[color][f - 1] > 0) ||
                                         (f < 7 && pawnFileCounts[color][f + 1] > 0);
            if (!hasNeighborFile) {
                mgScore -= sign * 11;
                egScore -= sign * 14;
            }

            bool passed = true;
            U64 enemies = enemyPawns;
            while (enemies) {
                const int e = pop_lsb(enemies);
                if (std::abs(file_of(e) - f) > 1) continue;
                const int er = rank_of(e);
                if ((color == WHITE && er > r) || (color == BLACK && er < r)) {
                    passed = false;
                    break;
                }
            }
            if (passed) {
                const int bonus = passedBonus[relativeRank];
                const bool supported = (pawnAttacks[color ^ 1][sq] & ownPawns) != 0;
                mgScore += sign * (bonus / 2 + (supported ? 8 : 0));
                egScore += sign * (bonus + (supported ? 14 : 0));
            }
        }
    }

    for (int color = WHITE; color <= BLACK; ++color) {
        const int sign = color == WHITE ? 1 : -1;
        if (popcount(p.pieces[color][BISHOP]) >= 2) {
            mgScore += sign * 28;
            egScore += sign * 36;
        }

        // Mobility and rook activity.
        for (int type = KNIGHT; type <= QUEEN; ++type) {
            U64 men = p.pieces[color][type];
            while (men) {
                const int sq = pop_lsb(men);
                U64 attacks = 0;
                if (type == KNIGHT) attacks = knightAttacks[sq];
                else if (type == BISHOP) attacks = bishop_attacks(sq, p.all);
                else if (type == ROOK) attacks = rook_attacks(sq, p.all);
                else attacks = bishop_attacks(sq, p.all) | rook_attacks(sq, p.all);
                const int mobility = popcount(attacks & ~p.occupied[color]);
                const int weight = type == KNIGHT || type == BISHOP ? 4 : (type == ROOK ? 2 : 1);
                mgScore += sign * mobility * weight;
                egScore += sign * mobility * std::max(1, weight / 2);

                if (type == ROOK) {
                    bool ownPawn = false, enemyPawn = false;
                    for (int r = 0; r < 8; ++r) {
                        const int onFile = r * 8 + file_of(sq);
                        ownPawn |= (p.pieces[color][PAWN] & bit(onFile)) != 0;
                        enemyPawn |= (p.pieces[color ^ 1][PAWN] & bit(onFile)) != 0;
                    }
                    if (!ownPawn) {
                        const int bonus = enemyPawn ? 9 : 17;
                        mgScore += sign * bonus;
                        egScore += sign * (bonus + 3);
                    }
                    const int relativeRank = color == WHITE ? rank_of(sq) : 7 - rank_of(sq);
                    if (relativeRank == 6) {
                        mgScore += sign * 13;
                        egScore += sign * 18;
                    }
                }
            }
        }

        // A compact king-shelter and king-ring danger term.
        const int king = p.king_square(color);
        if (king >= 0) {
            const int forward = color == WHITE ? 8 : -8;
            int shelter = 0;
            for (int df = -1; df <= 1; ++df) {
                const int f = file_of(king) + df;
                if (f < 0 || f >= 8) continue;
                const int one = king + forward + df;
                const int two = king + 2 * forward + df;
                if (one >= 0 && one < 64 && p.board[one] == make_piece(color, PAWN)) shelter += 11;
                else if (two >= 0 && two < 64 && p.board[two] == make_piece(color, PAWN)) shelter += 5;
                else shelter -= 7;
            }
            mgScore += sign * shelter;

            const U64 ring = kingAttacks[king] | bit(king);
            const int enemy = color ^ 1;
            U64 attacks = 0;
            U64 men = p.pieces[enemy][PAWN];
            while (men) attacks |= pawnAttacks[enemy][pop_lsb(men)];
            men = p.pieces[enemy][KNIGHT];
            while (men) attacks |= knightAttacks[pop_lsb(men)];
            men = p.pieces[enemy][BISHOP];
            while (men) attacks |= bishop_attacks(pop_lsb(men), p.all);
            men = p.pieces[enemy][ROOK];
            while (men) attacks |= rook_attacks(pop_lsb(men), p.all);
            men = p.pieces[enemy][QUEEN];
            while (men) {
                const int s = pop_lsb(men);
                attacks |= rook_attacks(s, p.all) | bishop_attacks(s, p.all);
            }
            const int danger = std::min(6, popcount(attacks & ring));
            mgScore -= sign * danger * 8;
        }
    }

    phase = std::min(24, phase);
    int score = (mgScore * phase + egScore * (24 - phase)) / 24;
    score += p.side == WHITE ? 10 : -10; // tempo
    return p.side == WHITE ? score : -score;
}

struct TTEntry {
    U64 key = 0;
    std::uint32_t move = 0;
    std::int16_t score = 0;
    std::int8_t depth = -1;
    std::uint8_t bound = 0; // 1 exact, 2 lower, 3 upper
    std::uint8_t age = 0;
};

class TranspositionTable {
public:
    void resize_mb(int megabytes) {
        megabytes = std::max(1, std::min(megabytes, 1024));
        const std::size_t bytes = static_cast<std::size_t>(megabytes) * 1024 * 1024;
        std::size_t count = 1;
        while ((count << 1) <= bytes / sizeof(TTEntry)) count <<= 1;
        entries_.assign(count, TTEntry{});
        mask_ = count - 1;
    }

    void clear() {
        std::fill(entries_.begin(), entries_.end(), TTEntry{});
    }

    void new_search() { ++age_; }
    std::uint8_t age() const { return age_; }

    TTEntry* probe(U64 key) {
        if (entries_.empty()) return nullptr;
        TTEntry& e = entries_[static_cast<std::size_t>(key) & mask_];
        return e.bound != 0 && e.key == key ? &e : nullptr;
    }

    void store(U64 key, Move move, int score, int depth, std::uint8_t bound, int ply) {
        if (entries_.empty()) return;
        TTEntry& e = entries_[static_cast<std::size_t>(key) & mask_];
        const bool replace = e.bound == 0 || e.key == key || e.age != age_ || depth >= e.depth - 2;
        if (!replace) return;
        if (score > MATE_THRESHOLD) score += ply;
        else if (score < -MATE_THRESHOLD) score -= ply;
        score = std::max(-32767, std::min(32767, score));
        e.key = key;
        e.move = move.code();
        e.score = static_cast<std::int16_t>(score);
        e.depth = static_cast<std::int8_t>(std::max(-1, std::min(depth, 127)));
        e.bound = bound;
        e.age = age_;
    }

    int hashfull() const {
        if (entries_.empty()) return 0;
        const std::size_t sample = std::min<std::size_t>(1000, entries_.size());
        int used = 0;
        for (std::size_t i = 0; i < sample; ++i)
            if (entries_[i].bound && entries_[i].age == age_) ++used;
        return sample ? used * 1000 / static_cast<int>(sample) : 0;
    }

private:
    std::vector<TTEntry> entries_;
    std::size_t mask_ = 0;
    std::uint8_t age_ = 0;
};

struct Limits {
    int depth = 64;
    std::uint64_t nodes = 0;
    int moveTimeMs = 0;
    int wtime = -1;
    int btime = -1;
    int winc = 0;
    int binc = 0;
    int movesToGo = 0;
    bool infinite = false;
};

struct SearchResult {
    Move bestMove{};
    int score = 0;
    int depth = 0;
    std::uint64_t nodes = 0;
};

class Searcher {
public:
    using Emit = std::function<void(const std::string&)>;

    Searcher(TranspositionTable& tt, std::atomic<bool>& stop, const Limits& limits, Emit emit)
        : tt_(tt), stop_(stop), limits_(limits), emit_(std::move(emit)) {
        for (auto& row : killers_) row.fill(Move{});
        std::memset(history_, 0, sizeof(history_));
        start_ = Clock::now();
        setup_time();
    }

    SearchResult run(Position root) {
        SearchResult result;
        MoveList rootMoves;
        generate_legal(root, rootMoves);
        if (rootMoves.size == 0) return result;
        result.bestMove = rootMoves[0];
        rootHistoryIndex_ = static_cast<int>(root.keyHistory.size()) - 1;
        setup_clock_for_side(root.side);
        tt_.new_search();
        int previousScore = 0;
        const int maxDepth = std::max(1, std::min(limits_.depth, MAX_PLY - 2));

        for (int depth = 1; depth <= maxDepth; ++depth) {
            if (poll_stop()) break;
            selDepth_ = 0;
            for (int i = 0; i < MAX_PLY; ++i) pvLength_[i] = i;
            int alpha = -INF;
            int beta = INF;
            int window = 28;
            if (depth >= 4) {
                alpha = std::max(-INF, previousScore - window);
                beta = std::min(INF, previousScore + window);
            }

            int score = 0;
            while (true) {
                score = negamax(root, depth, alpha, beta, 0, true, true);
                if (aborted_) break;
                if (score <= alpha && alpha > -INF) {
                    window *= 2;
                    alpha = std::max(-INF, score - window);
                    beta = std::min(INF, score + window / 2);
                    continue;
                }
                if (score >= beta && beta < INF) {
                    window *= 2;
                    alpha = std::max(-INF, score - window / 2);
                    beta = std::min(INF, score + window);
                    continue;
                }
                break;
            }
            if (aborted_) break;

            previousScore = score;
            result.score = score;
            result.depth = depth;
            result.nodes = nodes_;
            if (pvLength_[0] > 0) result.bestMove = pv_[0][0];
            emit_info(depth, score);
            if (softTimeMs_ > 0 && elapsed_ms() >= softTimeMs_) break;
            if (std::abs(score) >= MATE - depth) break;
        }
        result.nodes = nodes_;
        return result;
    }

private:
    TranspositionTable& tt_;
    std::atomic<bool>& stop_;
    Limits limits_;
    Emit emit_;
    Clock::time_point start_{};
    int softTimeMs_ = 0;
    int hardTimeMs_ = 0;
    std::uint64_t nodes_ = 0;
    int selDepth_ = 0;
    int rootHistoryIndex_ = 0;
    bool aborted_ = false;
    std::array<std::array<Move, 2>, MAX_PLY> killers_{};
    int history_[2][64][64]{};
    Move pv_[MAX_PLY][MAX_PLY]{};
    int pvLength_[MAX_PLY]{};

    void setup_time() {
        if (limits_.moveTimeMs > 0) {
            hardTimeMs_ = std::max(1, limits_.moveTimeMs - std::min(15, limits_.moveTimeMs / 10));
            softTimeMs_ = hardTimeMs_;
            return;
        }
        // Clock allocation depends on the side to move, which is known in run().
    }

    void setup_clock_for_side(int side) {
        if (limits_.infinite || limits_.moveTimeMs > 0) return;
        const int remaining = side == WHITE ? limits_.wtime : limits_.btime;
        const int increment = side == WHITE ? limits_.winc : limits_.binc;
        if (remaining < 0) return;
        const int overhead = 25;
        const int usable = std::max(1, remaining - overhead);
        const int moves = limits_.movesToGo > 0 ? limits_.movesToGo : 30;
        const int base = usable / std::max(1, moves) + (increment * 3) / 4;
        softTimeMs_ = std::max(5, std::min(usable, base));
        hardTimeMs_ = std::max(softTimeMs_, std::min(usable, base * 3));
    }

    std::int64_t elapsed_ms() const {
        return std::chrono::duration_cast<std::chrono::milliseconds>(Clock::now() - start_).count();
    }

    bool poll_stop() {
        if (aborted_) return true;
        if (stop_.load(std::memory_order_relaxed)) {
            aborted_ = true;
            return true;
        }
        if (limits_.nodes && nodes_ >= limits_.nodes) {
            aborted_ = true;
            return true;
        }
        if ((nodes_ & 1023ULL) == 0 && hardTimeMs_ > 0 && elapsed_ms() >= hardTimeMs_) {
            aborted_ = true;
            return true;
        }
        return false;
    }

    int score_from_tt(int score, int ply) const {
        if (score > MATE_THRESHOLD) return score - ply;
        if (score < -MATE_THRESHOLD) return score + ply;
        return score;
    }

    int move_score(const Position& p, Move m, Move ttMove, int ply) const {
        if (m == ttMove && static_cast<bool>(ttMove)) return 2'000'000;
        const int moving = p.board[m.from];
        const int movingType = piece_type(moving);
        int victim = p.board[m.to];
        if (movingType == PAWN && m.to == p.ep && victim == NO_PIECE && file_of(m.from) != file_of(m.to))
            victim = make_piece(p.side ^ 1, PAWN);
        if (victim != NO_PIECE) {
            static constexpr int values[6] = {100, 320, 330, 500, 900, 20000};
            int score = 1'000'000 + values[piece_type(victim)] * 16 - values[movingType];
            if (m.promotion) score += 800'000 + values[m.promotion];
            return score;
        }
        if (m.promotion) return 1'500'000 + m.promotion * 100;
        if (ply < MAX_PLY) {
            if (m == killers_[ply][0]) return 900'000;
            if (m == killers_[ply][1]) return 890'000;
        }
        return history_[p.side][m.from][m.to];
    }

    bool is_capture(const Position& p, Move m) const {
        if (p.board[m.to] != NO_PIECE) return true;
        const int piece = p.board[m.from];
        return piece_type(piece) == PAWN && m.to == p.ep && file_of(m.from) != file_of(m.to);
    }

    void order_moves(const Position& p, MoveList& moves, Move ttMove, int ply) const {
        std::array<int, 256> scores{};
        for (int i = 0; i < moves.size; ++i) scores[i] = move_score(p, moves[i], ttMove, ply);
        for (int i = 0; i < moves.size; ++i) {
            int best = i;
            for (int j = i + 1; j < moves.size; ++j)
                if (scores[j] > scores[best]) best = j;
            if (best != i) {
                std::swap(scores[i], scores[best]);
                std::swap(moves[i], moves[best]);
            }
        }
    }

    void update_quiet_cutoff(int side, Move cutoff, int depth, int ply,
                             const std::array<Move, 256>& tried, int triedCount) {
        if (ply < MAX_PLY) {
            if (killers_[ply][0] != cutoff) {
                killers_[ply][1] = killers_[ply][0];
                killers_[ply][0] = cutoff;
            }
        }
        const int bonus = std::min(2048, depth * depth * 24);
        int& h = history_[side][cutoff.from][cutoff.to];
        h = std::max(-16000, std::min(16000, h + bonus - h * std::abs(bonus) / 16384));
        for (int i = 0; i < triedCount; ++i) {
            const Move m = tried[i];
            if (m == cutoff) continue;
            int& old = history_[side][m.from][m.to];
            old = std::max(-16000, std::min(16000, old - bonus / 2));
        }
    }

    int negamax(Position& p, int depth, int alpha, int beta, int ply, bool pvNode, bool allowNull) {
        if (poll_stop()) return 0;
        ++nodes_;
        selDepth_ = std::max(selDepth_, ply);
        if ((nodes_ & 1023ULL) == 0 && poll_stop()) return 0;
        if (ply >= MAX_PLY - 1) return evaluate(p);

        pvLength_[ply] = ply;
        const bool inCheck = p.in_check(p.side);
        const bool drawn = (p.nullDepth == 0 && p.halfmove >= 100) ||
                           p.repetition(rootHistoryIndex_) || p.insufficient_material();
        if (drawn && !inCheck) return 0;
        if (depth <= 0 && !inCheck) return qsearch(p, alpha, beta, ply);
        if (inCheck) ++depth;
        if (depth <= 0) return qsearch(p, alpha, beta, ply);

        const int originalAlpha = alpha;
        Move ttMove{};
        TTEntry* entry = tt_.probe(p.key);
        if (entry) {
            ttMove = Move::from_code(entry->move);
            if (ply > 0 && !pvNode && entry->depth >= depth) {
                const int ttScore = score_from_tt(entry->score, ply);
                if (entry->bound == 1) return ttScore;
                if (entry->bound == 2 && ttScore >= beta) return ttScore;
                if (entry->bound == 3 && ttScore <= alpha) return ttScore;
            }
        }

        const int staticEval = inCheck ? -INF : evaluate(p);
        if (!inCheck && !pvNode && depth <= 3 && staticEval - (90 + depth * 100) >= beta)
            return staticEval;
        if (!inCheck && !pvNode && depth == 1 && staticEval + 180 <= alpha) {
            const int q = qsearch(p, alpha, beta, ply);
            if (q <= alpha) return q;
        }

        const bool hasNonPawn = (p.pieces[p.side][KNIGHT] | p.pieces[p.side][BISHOP] |
                                 p.pieces[p.side][ROOK] | p.pieces[p.side][QUEEN]) != 0;
        if (allowNull && !pvNode && !inCheck && depth >= 3 && hasNonPawn && staticEval >= beta) {
            NullUndo u;
            p.make_null(u);
            const int reduction = 2 + (depth >= 7 ? 1 : 0);
            int score = -negamax(p, depth - 1 - reduction, -beta, -beta + 1, ply + 1, false, false);
            p.undo_null(u);
            if (aborted_) return 0;
            if (score >= beta) {
                if (depth >= 7) {
                    const int verify = negamax(p, depth - reduction, beta - 1, beta, ply, false, false);
                    if (aborted_) return 0;
                    if (verify >= beta) return verify;
                } else {
                    return score;
                }
            }
        }

        MoveList moves;
        generate_legal(p, moves);
        if (moves.size == 0) return inCheck ? -MATE + ply : 0;
        if (drawn) return 0; // Preserve checkmate precedence at the fifty-move/repetition boundary.
        order_moves(p, moves, ttMove, ply);

        int bestScore = -INF;
        Move bestMove{};
        int searched = 0;
        std::array<Move, 256> quietTried{};
        int quietTriedCount = 0;
        const int us = p.side;

        for (int i = 0; i < moves.size; ++i) {
            if (poll_stop()) return 0;
            const Move m = moves[i];
            const bool capture = is_capture(p, m);
            const bool quiet = !capture && m.promotion == 0;
            if (!inCheck && !pvNode && searched > 0 && quiet && depth <= 3 &&
                staticEval + 115 * depth <= alpha) continue;
            if (!inCheck && !pvNode && searched >= 5 + depth * 3 && depth <= 3 && quiet) continue;

            Undo u;
            p.make_move(m, u);
            int score;
            if (searched == 0) {
                score = -negamax(p, depth - 1, -beta, -alpha, ply + 1, pvNode, true);
            } else {
                int reduction = 0;
                if (depth >= 3 && searched >= 3 && quiet && !inCheck) {
                    reduction = 1 + (depth >= 6 ? 1 : 0) + (searched >= 8 ? 1 : 0);
                    if (pvNode) reduction = std::max(1, reduction - 1);
                    if (history_[us][m.from][m.to] > 5000) reduction = std::max(1, reduction - 1);
                    reduction = std::min(reduction, depth - 2);
                }
                score = -negamax(p, depth - 1 - reduction, -alpha - 1, -alpha,
                                 ply + 1, false, true);
                if (!aborted_ && score > alpha && reduction > 0)
                    score = -negamax(p, depth - 1, -alpha - 1, -alpha, ply + 1, false, true);
                if (!aborted_ && score > alpha && score < beta && pvNode)
                    score = -negamax(p, depth - 1, -beta, -alpha, ply + 1, true, true);
            }
            p.undo_move(m, u);
            if (aborted_) return 0;

            ++searched;
            if (quiet && quietTriedCount < static_cast<int>(quietTried.size()))
                quietTried[quietTriedCount++] = m;
            if (score > bestScore) {
                bestScore = score;
                bestMove = m;
            }
            if (score > alpha) {
                alpha = score;
                if (ply == 0 || pvNode) {
                    pv_[ply][ply] = m;
                    for (int j = ply + 1; j < pvLength_[ply + 1]; ++j)
                        pv_[ply][j] = pv_[ply + 1][j];
                    pvLength_[ply] = pvLength_[ply + 1];
                }
            }
            if (alpha >= beta) {
                if (quiet) update_quiet_cutoff(us, m, depth, ply, quietTried, quietTriedCount);
                break;
            }
        }

        if (searched == 0) bestScore = alpha;
        std::uint8_t bound = 1;
        if (bestScore <= originalAlpha) bound = 3;
        else if (bestScore >= beta) bound = 2;
        tt_.store(p.key, bestMove, bestScore, depth, bound, ply);
        return bestScore;
    }

    int qsearch(Position& p, int alpha, int beta, int ply) {
        if (poll_stop()) return 0;
        ++nodes_;
        selDepth_ = std::max(selDepth_, ply);
        if ((nodes_ & 1023ULL) == 0 && poll_stop()) return 0;
        if (ply >= MAX_PLY - 1) return evaluate(p);
        pvLength_[ply] = ply;

        const bool inCheck = p.in_check(p.side);
        const bool drawn = (p.nullDepth == 0 && p.halfmove >= 100) ||
                           p.repetition(rootHistoryIndex_) || p.insufficient_material();
        if (drawn && !inCheck) return 0;
        const int standPat = inCheck ? -INF : evaluate(p);
        if (!inCheck) {
            if (standPat >= beta) return standPat;
            if (standPat > alpha) alpha = standPat;
        }

        MoveList moves;
        generate_legal(p, moves, !inCheck);
        if (inCheck && moves.size == 0) return -MATE + ply;
        if (!inCheck && moves.size == 0) {
            MoveList allLegal;
            generate_legal(p, allLegal, false);
            if (allLegal.size == 0) return 0;
        }
        if (drawn) return 0;
        order_moves(p, moves, Move{}, ply);
        for (int i = 0; i < moves.size; ++i) {
            if (poll_stop()) return 0;
            const Move m = moves[i];
            Undo u;
            p.make_move(m, u);
            const int score = -qsearch(p, -beta, -alpha, ply + 1);
            p.undo_move(m, u);
            if (aborted_) return 0;
            if (score >= beta) return score;
            if (score > alpha) {
                alpha = score;
                pv_[ply][ply] = m;
                for (int j = ply + 1; j < pvLength_[ply + 1]; ++j)
                    pv_[ply][j] = pv_[ply + 1][j];
                pvLength_[ply] = pvLength_[ply + 1];
            }
        }
        return alpha;
    }

    std::string score_string(int score) const {
        std::ostringstream out;
        if (std::abs(score) >= MATE_THRESHOLD) {
            int moves = (MATE - std::abs(score) + 1) / 2;
            if (score < 0) moves = -moves;
            out << "mate " << moves;
        } else {
            out << "cp " << score;
        }
        return out.str();
    }

    void emit_info(int depth, int score) {
        std::ostringstream out;
        const auto elapsed = std::max<std::int64_t>(1, elapsed_ms());
        const std::uint64_t nps = nodes_ * 1000ULL / static_cast<std::uint64_t>(elapsed);
        out << "info depth " << depth << " seldepth " << selDepth_ << " score " << score_string(score)
            << " nodes " << nodes_ << " nps " << nps << " hashfull " << tt_.hashfull()
            << " time " << elapsed << " pv";
        for (int i = 0; i < pvLength_[0]; ++i) out << ' ' << move_to_string(pv_[0][i]);
        emit_(out.str());
    }
};

std::mutex outputMutex;
void print_line(const std::string& line) {
    std::lock_guard<std::mutex> lock(outputMutex);
    std::cout << line << std::endl;
}

class Engine {
public:
    Engine() {
        init_tables();
        parse_fen(START_FEN, position_);
        tt_.resize_mb(32);
    }

    ~Engine() { stop_and_join(); }

    void stop_and_join() {
        if (worker_.joinable()) {
            stop_.store(true, std::memory_order_relaxed);
            worker_.join();
        }
    }

    void start_search(const Limits& limits) {
        stop_and_join();
        stop_.store(false, std::memory_order_relaxed);
        Position root = position_;
        worker_ = std::thread([this, root = std::move(root), limits]() mutable {
            Searcher searcher(tt_, stop_, limits, [](const std::string& line) { print_line(line); });
            SearchResult result = searcher.run(std::move(root));
            print_line("bestmove " + (result.bestMove ? move_to_string(result.bestMove) : std::string("0000")));
        });
    }

    void set_position(const std::string& command) {
        stop_and_join();
        std::istringstream in(command);
        std::string token;
        in >> token; // position
        in >> token;
        Position candidate;
        std::string error;
        bool ok = false;
        if (token == "startpos") {
            ok = parse_fen(START_FEN, candidate, &error);
        } else if (token == "fen") {
            std::string fen;
            while (in >> token && token != "moves") {
                if (!fen.empty()) fen += ' ';
                fen += token;
            }
            ok = parse_fen(fen, candidate, &error);
        } else {
            error = "Expected startpos or fen after position";
        }
        if (!ok) {
            std::cerr << "info string invalid position: " << error << '\n';
            return;
        }
        if (token != "moves") {
            // For startpos, token currently still contains "startpos"; consume the rest.
            std::string maybe;
            while (in >> maybe) {
                if (maybe == "moves") { token = maybe; break; }
            }
        }
        if (token == "moves") {
            std::string moveText;
            while (in >> moveText) {
                Move m;
                if (!parse_uci_move(candidate, moveText, m)) {
                    std::cerr << "info string ignored illegal move in position: " << moveText << '\n';
                    break;
                }
                Undo u;
                candidate.make_move(m, u);
            }
        }
        position_ = std::move(candidate);
    }

    void set_option(const std::string& command) {
        stop_and_join();
        std::istringstream in(command);
        std::string token;
        in >> token; // setoption
        in >> token; // name
        std::string name;
        std::string value;
        bool readingValue = false;
        while (in >> token) {
            if (token == "value") { readingValue = true; continue; }
            if (readingValue) {
                if (!value.empty()) value += ' ';
                value += token;
            } else {
                if (!name.empty()) name += ' ';
                name += token;
            }
        }
        if (name == "Hash") {
            try { tt_.resize_mb(std::stoi(value)); }
            catch (...) { std::cerr << "info string Hash expects an integer\n"; }
        } else if (name == "Clear Hash") {
            tt_.clear();
        }
    }

    void go(const std::string& command) {
        std::istringstream in(command);
        std::string token;
        in >> token; // go
        Limits limits;
        bool hasConstraint = false;
        while (in >> token) {
            if (token == "depth") {
                in >> limits.depth;
                limits.depth = std::max(1, std::min(limits.depth, MAX_PLY - 2));
                hasConstraint = true;
            } else if (token == "nodes") {
                in >> limits.nodes;
                hasConstraint = true;
            } else if (token == "movetime") {
                in >> limits.moveTimeMs;
                hasConstraint = true;
            } else if (token == "wtime") in >> limits.wtime;
            else if (token == "btime") in >> limits.btime;
            else if (token == "winc") in >> limits.winc;
            else if (token == "binc") in >> limits.binc;
            else if (token == "movestogo") in >> limits.movesToGo;
            else if (token == "infinite" || token == "ponder") limits.infinite = true;
        }
        if (!hasConstraint && limits.wtime < 0 && limits.btime < 0) limits.infinite = true;
        start_search(limits);
    }

    void go_perft(int depth) {
        stop_and_join();
        Position copy = position_;
        const auto start = Clock::now();
        const std::uint64_t nodes = perft(copy, depth);
        const auto ms = std::max<std::int64_t>(1,
            std::chrono::duration_cast<std::chrono::milliseconds>(Clock::now() - start).count());
        print_line("info string perft depth " + std::to_string(depth) + " nodes " +
                   std::to_string(nodes) + " time " + std::to_string(ms) + " nps " +
                   std::to_string(nodes * 1000ULL / static_cast<std::uint64_t>(ms)));
    }

    void uci_loop() {
        std::string line;
        while (std::getline(std::cin, line)) {
            std::istringstream in(line);
            std::string command;
            in >> command;
            if (command.empty()) continue;
            if (command == "uci") {
                print_line("id name Mitra 0.1");
                print_line("id author Arena chess-engine project");
                print_line("option name Hash type spin default 32 min 1 max 1024");
                print_line("option name Clear Hash type button");
                print_line("uciok");
            } else if (command == "isready") {
                print_line("readyok");
            } else if (command == "ucinewgame") {
                stop_and_join();
                parse_fen(START_FEN, position_);
                tt_.clear();
            } else if (command == "position") {
                set_position(line);
            } else if (command == "setoption") {
                set_option(line);
            } else if (command == "go") {
                if (line.find("perft") != std::string::npos) {
                    std::istringstream args(line);
                    std::string word;
                    int depth = 1;
                    while (args >> word) if (word == "perft") args >> depth;
                    go_perft(std::max(0, std::min(depth, 20)));
                } else {
                    go(line);
                }
            } else if (command == "stop") {
                stop_and_join();
            } else if (command == "quit") {
                stop_and_join();
                break;
            } else if (command == "d") {
                display_position();
            }
        }
        stop_and_join();
    }

    void display_position() const {
        for (int r = 7; r >= 0; --r) {
            std::ostringstream row;
            row << (r + 1) << "  ";
            for (int f = 0; f < 8; ++f) {
                const int p = position_.board[r * 8 + f];
                char c = '.';
                if (p) {
                    static constexpr char symbols[] = "PNBRQK";
                    c = symbols[piece_type(p)];
                    if (piece_color(p) == BLACK) c = static_cast<char>(std::tolower(c));
                }
                row << c << ' ';
            }
            std::cerr << row.str() << '\n';
        }
        std::cerr << "   a b c d e f g h\n";
    }

    Position& position() { return position_; }
    TranspositionTable& tt() { return tt_; }

private:
    Position position_;
    TranspositionTable tt_;
    std::atomic<bool> stop_{false};
    std::thread worker_;
};

bool run_selftest() {
    init_tables();
    struct Test { const char* fen; int depth; std::uint64_t expected; const char* name; };
    const Test tests[] = {
        {START_FEN, 1, 20, "start position depth 1"},
        {START_FEN, 2, 400, "start position depth 2"},
        {START_FEN, 3, 8902, "start position depth 3"},
        {START_FEN, 4, 197281, "start position depth 4"},
        {START_FEN, 5, 4865609, "start position depth 5"},
        {"r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", 1, 48, "Kiwipete depth 1"},
        {"r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", 2, 2039, "Kiwipete depth 2"},
        {"r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", 3, 97862, "Kiwipete depth 3"},
        {"r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", 4, 4085603, "Kiwipete depth 4"},
        {"8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", 1, 14, "endgame/en-passant depth 1"},
        {"8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", 2, 191, "endgame/en-passant depth 2"},
        {"8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", 3, 2812, "endgame/en-passant depth 3"},
        {"8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", 4, 43238, "endgame/en-passant depth 4"},
        {"r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1", 1, 6, "promotions/castling depth 1"},
        {"r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1", 2, 264, "promotions/castling depth 2"},
        {"r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1", 3, 9467, "promotions/castling depth 3"},
        {"r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1", 4, 422333, "promotions/castling depth 4"},
        {"rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8", 3, 62379, "promotion/check depth 3"},
        {"rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8", 4, 2103487, "promotion/check depth 4"}
    };
    bool ok = true;
    for (const Test& t : tests) {
        Position p;
        std::string error;
        if (!parse_fen(t.fen, p, &error)) {
            std::cerr << "FAIL " << t.name << ": " << error << '\n';
            ok = false;
            continue;
        }
        const std::uint64_t actual = perft(p, t.depth);
        if (actual != t.expected) {
            std::cerr << "FAIL " << t.name << ": expected " << t.expected << ", got " << actual << '\n';
            ok = false;
        } else {
            std::cout << "PASS " << t.name << " = " << actual << '\n';
        }
    }
    if (!ok) return false;

    Position p;
    parse_fen(START_FEN, p);
    Move m;
    if (!parse_uci_move(p, "e2e4", m)) {
        std::cerr << "FAIL UCI move parsing\n";
        return false;
    }
    Undo u;
    p.make_move(m, u);
    if (p.key != p.recompute_key() || p.side != BLACK || p.ep != 20) {
        std::cerr << "FAIL make-move hash/en-passant state\n";
        return false;
    }
    p.undo_move(m, u);
    if (p.key != p.recompute_key() || p.side != WHITE || p.board[12] != make_piece(WHITE, PAWN)) {
        std::cerr << "FAIL unmake-move state restoration\n";
        return false;
    }
    std::cout << "PASS make/unmake and incremental hash\n";

    Position matePosition, stalematePosition;
    if (!parse_fen("7k/6Q1/6K1/8/8/8/8/8 b - - 0 1", matePosition) ||
        !parse_fen("7k/5Q2/6K1/8/8/8/8/8 b - - 0 1", stalematePosition)) {
        std::cerr << "FAIL terminal-position FEN parsing\n";
        return false;
    }
    MoveList terminalMoves;
    generate_legal(matePosition, terminalMoves);
    if (terminalMoves.size != 0 || !matePosition.in_check(BLACK)) {
        std::cerr << "FAIL checkmate detection\n";
        return false;
    }
    generate_legal(stalematePosition, terminalMoves);
    if (terminalMoves.size != 0 || stalematePosition.in_check(BLACK)) {
        std::cerr << "FAIL stalemate detection\n";
        return false;
    }
    std::cout << "PASS checkmate and stalemate detection\n";
    return true;
}

void run_bench(int depth) {
    init_tables();
    Position p;
    parse_fen(START_FEN, p);
    TranspositionTable tt;
    tt.resize_mb(32);
    std::atomic<bool> stop{false};
    Limits limits;
    limits.depth = std::max(1, std::min(depth, 16));
    Searcher searcher(tt, stop, limits, [](const std::string& line) { std::cout << line << '\n'; });
    const SearchResult result = searcher.run(p);
    std::cout << "bestmove " << (result.bestMove ? move_to_string(result.bestMove) : "0000") << '\n';
}

} // namespace

int main(int argc, char** argv) {
    init_tables();
    if (argc >= 2 && std::string(argv[1]) == "--selftest")
        return run_selftest() ? 0 : 1;
    if (argc >= 2 && std::string(argv[1]) == "--bench") {
        const int depth = argc >= 3 ? std::atoi(argv[2]) : 6;
        run_bench(depth);
        return 0;
    }
    if (argc >= 2 && std::string(argv[1]) == "--perft") {
        if (argc < 3) {
            std::cerr << "usage: mitra --perft DEPTH [FEN]\n";
            return 2;
        }
        const int depth = std::max(0, std::min(20, std::atoi(argv[2])));
        std::string fen = START_FEN;
        if (argc >= 4) {
            fen.clear();
            for (int i = 3; i < argc; ++i) {
                if (!fen.empty()) fen += ' ';
                fen += argv[i];
            }
        }
        Position p;
        std::string error;
        if (!parse_fen(fen, p, &error)) {
            std::cerr << "invalid FEN: " << error << '\n';
            return 2;
        }
        std::cout << perft(p, depth) << '\n';
        return 0;
    }
    if (argc >= 2 && (std::string(argv[1]) == "--help" || std::string(argv[1]) == "-h")) {
        std::cout << "Mitra chess engine (UCI)\n"
                     "usage: mitra [--selftest | --bench [DEPTH] | --perft DEPTH [FEN]]\n";
        return 0;
    }

    Engine engine;
    engine.uci_loop();
    return 0;
}
