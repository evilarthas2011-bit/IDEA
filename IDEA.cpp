
#include <iostream>
#include <string>
#include <vector>
#include <array>
#include <cstdint>
#include <random>
#include <sstream>
#include <iomanip>
#include <algorithm>
#include <cctype>


class Idea {
public:
    static const size_t BLOCK_SIZE = 8;    // 64 bit
    static const size_t KEY_SIZE = 16;   // 128 bit

    explicit Idea(const std::array<uint8_t, KEY_SIZE>& key) {
        expandKey(key, enc_);
        invertKey(enc_, dec_);
    }

    void encryptBlock(const uint8_t* in, uint8_t* out) const { crypt(in, out, enc_); }
    void decryptBlock(const uint8_t* in, uint8_t* out) const { crypt(in, out, dec_); }

    const std::array<uint16_t, 52>& subkeys() const { return enc_; }

private:
    std::array<uint16_t, 52> enc_{}, dec_{};

    static const uint32_t MASK = 0xFFFFu;
    static const uint32_t MOD = 0x10001u;   // 65537

    // the three "incompatible" group operations on 16-bit words
    static uint16_t add(uint16_t a, uint16_t b) { return (uint16_t)((a + b) & MASK); }   // + mod 2^16
    static uint16_t xorw(uint16_t a, uint16_t b) { return (uint16_t)(a ^ b); }          // XOR
    static uint16_t mul(uint16_t a, uint16_t b) {                                       // * mod 2^16+1
        uint32_t x = (a == 0) ? 0x10000u : a;    
        uint32_t y = (b == 0) ? 0x10000u : b;
        uint64_t p = (uint64_t)x * y;           
        return (uint16_t)((p % MOD) & MASK);     // 2^16 in the result means 0x0000
    }
    static uint16_t addInv(uint16_t x) { return (uint16_t)((0u - x) & MASK); }
    static uint16_t mulInv(uint16_t x) {         // inverse mod 65537, extended Euclid
        if (x <= 1) return x;                    // 0 and 1 are self-inverse
        int32_t a = x, t0 = 1, t1 = (int32_t)(MOD / x), y = (int32_t)(MOD % x);
        while (y != 1) {
            int32_t q = a / y; a %= y; t0 += q * t1;
            if (a == 1) return (uint16_t)(t0 & MASK);
            q = y / a; y %= a; t1 += q * t0;
        }
        return (uint16_t)((1 - t1) & MASK);
    }

    //  key schedule: 52 subkeys, key rotated left by 25 bits every 8 subkeys 
    static uint16_t wordAt(const std::array<uint8_t, KEY_SIZE>& k, int bitPos) {
        uint16_t v = 0;
        for (int i = 0; i < 16; ++i) {
            int b = (bitPos + i) % 128;
            v = (uint16_t)((v << 1) | ((k[b / 8] >> (7 - (b % 8))) & 1));
        }
        return v;
    }
    static void expandKey(const std::array<uint8_t, KEY_SIZE>& key, std::array<uint16_t, 52>& z) {
        size_t idx = 0;
        for (int group = 0; group < 7 && idx < 52; ++group) {
            int shift = (25 * group) % 128;
            for (int j = 0; j < 8 && idx < 52; ++j)
                z[idx++] = wordAt(key, (shift + 16 * j) % 128);
        }
    }

    //  decryption subkeys: reversed order, inverted for * and + 
    static void invertKey(const std::array<uint16_t, 52>& e, std::array<uint16_t, 52>& d) {
        d[0] = mulInv(e[48]); d[1] = addInv(e[49]); d[2] = addInv(e[50]); d[3] = mulInv(e[51]);
        d[4] = e[46]; d[5] = e[47];
        size_t p = 6;
        for (int r = 7; r >= 1; --r) {
            int i = 6 * r;
            d[p] = mulInv(e[i]);
            d[p + 1] = addInv(e[i + 2]);   // -Z3 first ...
            d[p + 2] = addInv(e[i + 1]);   // ... then -Z2 (compensates the middle swap)
            d[p + 3] = mulInv(e[i + 3]);
            d[p + 4] = e[i - 2];
            d[p + 5] = e[i - 1];
            p += 6;
        }
        d[48] = mulInv(e[0]); d[49] = addInv(e[1]); d[50] = addInv(e[2]); d[51] = mulInv(e[3]);
    }

    // 8 rounds + output transformation; same code for enc and dec
    static void crypt(const uint8_t* in, uint8_t* out, const std::array<uint16_t, 52>& k) {
        uint16_t x1 = (uint16_t)((in[0] << 8) | in[1]);
        uint16_t x2 = (uint16_t)((in[2] << 8) | in[3]);
        uint16_t x3 = (uint16_t)((in[4] << 8) | in[5]);
        uint16_t x4 = (uint16_t)((in[6] << 8) | in[7]);
        size_t p = 0;
        for (int r = 0; r < 8; ++r) {
            uint16_t y1 = mul(x1, k[p]);
            uint16_t y2 = add(x2, k[p + 1]);
            uint16_t y3 = add(x3, k[p + 2]);
            uint16_t y4 = mul(x4, k[p + 3]);
            uint16_t t1 = xorw(y1, y3);
            uint16_t t2 = xorw(y2, y4);
            uint16_t s = mul(t1, k[p + 4]);
            uint16_t w = add(s, t2);
            uint16_t v = mul(w, k[p + 5]);
            uint16_t q = add(s, v);
            uint16_t o1 = xorw(y1, v), o2 = xorw(y2, q), o3 = xorw(y3, v), o4 = xorw(y4, q);
            x1 = o1; x4 = o4;
            if (r < 7) { x2 = o3; x3 = o2; }   // swap the two middle sub-blocks
            else { x2 = o2; x3 = o3; }   // last round: swap is cancelled
            p += 6;
        }
        uint16_t c1 = mul(x1, k[48]);          // output transformation ("half-round")
        uint16_t c2 = add(x2, k[49]);
        uint16_t c3 = add(x3, k[50]);
        uint16_t c4 = mul(x4, k[51]);
        out[0] = (uint8_t)(c1 >> 8); out[1] = (uint8_t)c1;
        out[2] = (uint8_t)(c2 >> 8); out[3] = (uint8_t)c2;
        out[4] = (uint8_t)(c3 >> 8); out[5] = (uint8_t)c3;
        out[6] = (uint8_t)(c4 >> 8); out[7] = (uint8_t)c4;
    }
};


static std::string toHex(const std::vector<uint8_t>& data) {
    std::ostringstream os;
    for (uint8_t b : data) os << std::uppercase << std::hex << std::setw(2) << std::setfill('0') << (int)b;
    return os.str();
}

static bool fromHex(const std::string& text, std::vector<uint8_t>& out) {
    std::string s;
    for (char c : text) if (!isspace((unsigned char)c)) s += c;
    if (s.empty() || s.size() % 2 != 0) return false;
    out.clear();
    for (size_t i = 0; i < s.size(); i += 2) {
        int hi = 0, lo = 0;
        auto nib = [](char c, int& v) {
            if (c >= '0' && c <= '9') { v = c - '0'; return true; }
            c = (char)toupper((unsigned char)c);
            if (c >= 'A' && c <= 'F') { v = c - 'A' + 10; return true; }
            return false;
            };
        if (!nib(s[i], hi) || !nib(s[i + 1], lo)) return false;
        out.push_back((uint8_t)((hi << 4) | lo));
    }
    return true;
}

static std::array<uint8_t, 16> keyFromHex(const std::string& hex) {
    std::vector<uint8_t> raw;
    fromHex(hex, raw);
    std::array<uint8_t, 16> k{};
    std::copy(raw.begin(), raw.end(), k.begin());
    return k;
}

// Educational passphrase -> 128-bit key folding (NOT a strong KDF, use hex key for real tests)
static std::array<uint8_t, 16> keyFromPassphrase(const std::string& pass) {
    uint64_t h1 = 0xcbf29ce484222325ULL, h2 = 0x9e3779b97f4a7c15ULL;
    for (int round = 0; round < 1000; ++round) {
        for (unsigned char c : pass) {
            h1 ^= c; h1 *= 0x100000001b3ULL;
            h2 ^= (uint64_t)c + (uint64_t)round; h2 *= 0x100000001b3ULL;
            h2 = (h2 << 7) | (h2 >> 57);
        }
        h1 ^= h2; h2 += h1 * 0x9e3779b97f4a7c15ULL;
    }
    std::array<uint8_t, 16> k{};
    for (int i = 0; i < 8; ++i) { k[i] = (uint8_t)(h1 >> (56 - 8 * i)); k[8 + i] = (uint8_t)(h2 >> (56 - 8 * i)); }
    return k;
}

static std::vector<uint8_t> randomBytes(size_t n) {
    std::random_device rd;
    std::vector<uint8_t> v(n);
    for (auto& b : v) b = (uint8_t)(rd() & 0xFF);
    return v;
}

// CBC + PKCS#7. Output = IV (8 bytes) || ciphertext
static std::vector<uint8_t> encryptText(const Idea& idea, const std::string& text) {
    std::vector<uint8_t> data(text.begin(), text.end());
    uint8_t pad = (uint8_t)(8 - data.size() % 8);          // 1..8, always adds padding
    data.insert(data.end(), pad, pad);

    std::vector<uint8_t> iv = randomBytes(8);
    std::vector<uint8_t> out = iv;
    std::array<uint8_t, 8> prev{}, buf{};
    std::copy(iv.begin(), iv.end(), prev.begin());
    for (size_t i = 0; i < data.size(); i += 8) {
        for (size_t j = 0; j < 8; ++j) buf[j] = (uint8_t)(data[i + j] ^ prev[j]);
        uint8_t c[8];
        idea.encryptBlock(buf.data(), c);
        out.insert(out.end(), c, c + 8);
        std::copy(c, c + 8, prev.begin());
    }
    return out;
}

static bool decryptText(const Idea& idea, const std::vector<uint8_t>& blob, std::string& text) {
    if (blob.size() < 16 || blob.size() % 8 != 0) return false;   // IV + at least one block
    std::array<uint8_t, 8> prev{}, cur{};
    std::copy(blob.begin(), blob.begin() + 8, prev.begin());
    std::vector<uint8_t> plain;
    for (size_t i = 8; i < blob.size(); i += 8) {
        std::copy(blob.begin() + i, blob.begin() + i + 8, cur.begin());
        uint8_t p[8];
        idea.decryptBlock(cur.data(), p);
        for (size_t j = 0; j < 8; ++j) plain.push_back((uint8_t)(p[j] ^ prev[j]));
        prev = cur;
    }
    uint8_t pad = plain.back();
    if (pad < 1 || pad > 8 || pad > plain.size()) return false;
    for (size_t i = plain.size() - pad; i < plain.size(); ++i)
        if (plain[i] != pad) return false;
    plain.resize(plain.size() - pad);
    text.assign(plain.begin(), plain.end());
    return true;
}

static void selfTest() {
    struct V { const char* key; const char* plain; const char* cipher; };
    const V vectors[] = {
        { "00010002000300040005000600070008", "0000000100020003", "11FBED2B01986DE5" },
        { "00010002000300040005000600070008", "0102030405060708", "540E5FEA18C2F8B1" },
        { "00010002000300040005000600070008", "0019324B647D96AF", "9F0A0AB6E10CED78" }
    };
    bool all = true;
    for (const auto& v : vectors) {
        Idea idea(keyFromHex(v.key));
        std::vector<uint8_t> p, expected;
        fromHex(v.plain, p);
        fromHex(v.cipher, expected);
        uint8_t c[8], back[8];
        idea.encryptBlock(p.data(), c);
        idea.decryptBlock(c, back);
        bool okEnc = std::equal(c, c + 8, expected.begin());
        bool okDec = std::equal(back, back + 8, p.begin());
        all = all && okEnc && okDec;
        std::cout << "  key=" << v.key << "  plain=" << v.plain
            << "  cipher=" << toHex(std::vector<uint8_t>(c, c + 8))
            << "  expected=" << v.cipher
            << "  encrypt=" << (okEnc ? "OK" : "FAIL")
            << "  decrypt=" << (okDec ? "OK" : "FAIL") << "\n";
    }
    std::cout << (all ? "  RESULT: all vectors passed\n" : "  RESULT: FAILED\n");
}

static void showKeySchedule(const Idea& idea) {
    const auto& z = idea.subkeys();
    for (int r = 0; r < 8; ++r) {
        std::cout << "  round " << (r + 1) << ": ";
        for (int j = 0; j < 6; ++j)
            std::cout << std::uppercase << std::hex << std::setw(4) << std::setfill('0') << z[r * 6 + j] << " ";
        std::cout << "\n";
    }
    std::cout << "  half-round: ";
    for (int j = 48; j < 52; ++j)
        std::cout << std::uppercase << std::hex << std::setw(4) << std::setfill('0') << z[j] << " ";
    std::cout << std::dec << "\n";
}


int main() {
    std::array<uint8_t, 16> key = keyFromHex("00010002000300040005000600070008");
    Idea idea(key);

    std::cout << " IDEA cipher: 64-bit block, 128-bit key, 8.5 rounds \n";
    for (;;) {
        std::cout << "\nCurrent key (hex): " << toHex(std::vector<uint8_t>(key.begin(), key.end())) << "\n"
            << "  1 - Encrypt text\n"
            << "  2 - Decrypt hex\n"
            << "  3 - Set key ( hex digits or a passphrase)\n"
            << "  4 - Show key schedule (52 subkeys)\n"
            << "  5 - Self-test (official test vectors)\n"
            << "  0 - Exit\n"
            << "Choice: ";
        std::string line;
        if (!std::getline(std::cin, line)) break;
        std::string choice = line;
        choice.erase(std::remove_if(choice.begin(), choice.end(),
            [](unsigned char c) { return isspace(c); }), choice.end());

        if (choice == "0") { std::cout << "Bye.\n"; break; }

        if (choice == "1") {
            std::cout << "Enter text (English): ";
            std::string text;
            if (!std::getline(std::cin, text)) break;
            if (text.empty()) { std::cout << "Empty input, nothing to encrypt.\n"; continue; }
            std::vector<uint8_t> blob = encryptText(idea, text);
            std::cout << "Ciphertext (hex, first 8 bytes = IV):\n" << toHex(blob) << "\n";
            std::string check;
            if (decryptText(idea, blob, check))
                std::cout << "Decrypted back (check): " << check << "\n";
            std::cout << "Blocks: " << (blob.size() - 8) / 8 << " (padding PKCS#7)\n";
        }
        else if (choice == "2") {
            std::cout << "Enter ciphertext (hex): ";
            std::string hex;
            if (!std::getline(std::cin, hex)) break;
            std::vector<uint8_t> blob;
            if (!fromHex(hex, blob)) { std::cout << "Invalid hex string.\n"; continue; }
            std::string text;
            if (decryptText(idea, blob, text)) std::cout << "Plaintext: " << text << "\n";
            else std::cout << "Decryption failed: wrong key, corrupted data or bad length.\n";
        }
        else if (choice == "3") {
            std::cout << "Enter  hex digits or a passphrase: ";
            std::string in;
            if (!std::getline(std::cin, in)) break;
            std::string clean;
            for (char c : in) if (!isspace((unsigned char)c)) clean += c;
            std::vector<uint8_t> raw;
            if (clean.size() == 32 && fromHex(clean, raw)) key = keyFromHex(clean);
            else if (!in.empty()) { key = keyFromPassphrase(in); std::cout << "Key derived from passphrase (educational KDF).\n"; }
            else { std::cout << "Empty key, keeping the old one.\n"; continue; }
            idea = Idea(key);
            std::cout << "New key: " << toHex(std::vector<uint8_t>(key.begin(), key.end())) << "\n";
        }
        else if (choice == "4") showKeySchedule(idea);
        else if (choice == "5") selfTest();
        else std::cout << "Unknown option.\n";
    }
    return 0;
}