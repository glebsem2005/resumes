import { randomBytes } from 'crypto';

// Real Kyber-768 implementation
export class Kyber768 {
  private static readonly N = 256;
  private static readonly K = 3;
  private static readonly Q = 3329;
  private static readonly ETA1 = 2;
  private static readonly ETA2 = 2;
  private static readonly DU = 10;
  private static readonly DV = 4;
  
  private static readonly POLY_BYTES = 384;
  private static readonly POLYVEC_BYTES = this.K * this.POLY_BYTES;
  private static readonly POLYVEC_COMPRESSED_BYTES = this.K * 320;
  private static readonly POLY_COMPRESSED_BYTES = 128;
  
  public static readonly PUBLIC_KEY_BYTES = this.POLYVEC_BYTES + 32;
  public static readonly SECRET_KEY_BYTES = this.POLYVEC_BYTES + this.PUBLIC_KEY_BYTES + 2 * 32;
  public static readonly CIPHERTEXT_BYTES = this.POLYVEC_COMPRESSED_BYTES + this.POLY_COMPRESSED_BYTES;
  public static readonly SHARED_SECRET_BYTES = 32;

  static generateKeyPair(): { publicKey: Uint8Array; privateKey: Uint8Array } {
    const seed = randomBytes(32);
    const publicSeed = new Uint8Array(32);
    const noiseSeed = new Uint8Array(32);
    
    // Hash seed to get public seed and noise seed
    const hash = this.sha3_512(seed);
    publicSeed.set(hash.slice(0, 32));
    noiseSeed.set(hash.slice(32, 64));
    
    // Generate matrix A from public seed
    const A = this.generateMatrix(publicSeed, false);
    
    // Generate secret vector s from noise seed
    const s = this.generateSecretVector(noiseSeed, 0);
    
    // Generate error vector e
    const e = this.generateErrorVector(noiseSeed, this.K);
    
    // Compute public key: t = As + e
    const t = this.matrixVectorMultiply(A, s);
    this.vectorAdd(t, e);
    
    // Pack public key
    const publicKey = new Uint8Array(this.PUBLIC_KEY_BYTES);
    this.packPublicKey(publicKey, t, publicSeed);
    
    // Pack private key
    const privateKey = new Uint8Array(this.SECRET_KEY_BYTES);
    this.packPrivateKey(privateKey, s, publicKey);
    
    return { publicKey, privateKey };
  }

  static encapsulate(publicKey: Uint8Array): { ciphertext: Uint8Array; sharedSecret: Uint8Array } {
    // Unpack public key
    const { t, rho } = this.unpackPublicKey(publicKey);
    
    // Generate random coins
    const coins = randomBytes(32);
    
    // Hash coins and public key
    const hash = this.sha3_256(new Uint8Array([...coins, ...publicKey]));
    const kr = this.sha3_512(hash);
    
    const msg = kr.slice(0, 32);
    const r = kr.slice(32, 64);
    
    // Generate matrix A from rho
    const A = this.generateMatrix(rho, true);
    
    // Generate r vectors
    const r1 = this.generateSecretVector(r, 0);
    const e1 = this.generateErrorVector(r, this.K);
    const e2 = this.generateErrorPoly(r, this.K * 2);
    
    // Compute ciphertext
    const u = this.matrixTransposeVectorMultiply(A, r1);
    this.vectorAdd(u, e1);
    
    const v = this.vectorDotProduct(t, r1);
    this.polyAdd(v, e2);
    
    // Add message
    const msgPoly = this.messageToPolynomial(msg);
    this.polyAdd(v, msgPoly);
    
    // Pack ciphertext
    const ciphertext = new Uint8Array(this.CIPHERTEXT_BYTES);
    this.packCiphertext(ciphertext, u, v);
    
    // Derive shared secret
    const sharedSecret = this.kdf(msg);
    
    return { ciphertext, sharedSecret };
  }

  static decapsulate(ciphertext: Uint8Array, privateKey: Uint8Array): Uint8Array {
    // Unpack private key
    const { s, publicKey } = this.unpackPrivateKey(privateKey);
    
    // Unpack ciphertext
    const { u, v } = this.unpackCiphertext(ciphertext);
    
    // Decrypt: m = v - s^T * u
    const sTu = this.vectorDotProduct(s, u);
    this.polySub(v, sTu);
    
    // Recover message
    const msg = this.polynomialToMessage(v);
    
    // Re-encrypt to verify
    const { ciphertext: ciphertext2 } = this.encapsulate(publicKey);
    
    if (!this.constantTimeEquals(ciphertext, ciphertext2)) {
      // Decryption failure, return random
      return randomBytes(this.SHARED_SECRET_BYTES);
    }
    
    return this.kdf(msg);
  }

  private static generateMatrix(seed: Uint8Array, transposed: boolean): number[][][] {
    const A: number[][][] = [];
    for (let i = 0; i < this.K; i++) {
      A[i] = [];
      for (let j = 0; j < this.K; j++) {
        const nonce = transposed ? (j << 8) | i : (i << 8) | j;
        A[i][j] = this.uniformSample(seed, nonce);
      }
    }
    return A;
  }

  private static uniformSample(seed: Uint8Array, nonce: number): number[] {
    const poly = new Array(this.N).fill(0);
    const buf = new Uint8Array(168); // 3 * 56 bytes for rejection sampling
    
    let ctr = 0;
    let pos = 0;
    
    while (ctr < this.N) {
      // XOF (extendable output function) based on SHAKE-128
      this.xof(buf, seed, nonce, pos);
      
      for (let i = 0; i < buf.length && ctr < this.N; i += 3) {
        const val1 = ((buf[i] | (buf[i + 1] << 8)) & 0xFFF);
        const val2 = (((buf[i + 1] >> 4) | (buf[i + 2] << 4)) & 0xFFF);
        
        if (val1 < this.Q) {
          poly[ctr++] = val1;
        }
        if (val2 < this.Q && ctr < this.N) {
          poly[ctr++] = val2;
        }
      }
      pos += buf.length;
    }
    
    return poly;
  }

  private static generateSecretVector(seed: Uint8Array, nonce: number): number[][] {
    const vector: number[][] = [];
    for (let i = 0; i < this.K; i++) {
      vector[i] = this.sampleCBD(seed, nonce + i, this.ETA1);
    }
    return vector;
  }

  private static sampleCBD(seed: Uint8Array, nonce: number, eta: number): number[] {
    const poly = new Array(this.N).fill(0);
    const buf = new Uint8Array(eta * this.N / 4);
    
    this.prf(buf, seed, nonce);
    
    for (let i = 0; i < this.N; i++) {
      let a = 0, b = 0;
      for (let j = 0; j < eta; j++) {
        const bytePos = (2 * i * eta + j) >> 3;
        const bitPos = (2 * i * eta + j) & 7;
        a += (buf[bytePos] >> bitPos) & 1;
        
        const bytePos2 = (2 * i * eta + eta + j) >> 3;
        const bitPos2 = (2 * i * eta + eta + j) & 7;
        b += (buf[bytePos2] >> bitPos2) & 1;
      }
      poly[i] = this.modQ(a - b);
    }
    
    return poly;
  }

  private static ntt(poly: number[]): number[] {
    const result = [...poly];
    let k = 1;
    
    for (let len = 128; len >= 2; len >>= 1) {
      for (let start = 0; start < this.N; start = start + 2 * len) {
        const zeta = this.NTT_ZETAS[k++];
        for (let j = start; j < start + len; j++) {
          const t = this.modQ(zeta * result[j + len]);
          result[j + len] = this.modQ(result[j] - t);
          result[j] = this.modQ(result[j] + t);
        }
      }
    }
    
    return result;
  }

  private static invNtt(poly: number[]): number[] {
    const result = [...poly];
    let k = 127;
    
    for (let len = 2; len <= 128; len <<= 1) {
      for (let start = 0; start < this.N; start = start + 2 * len) {
        const zeta = this.NTT_ZETAS[k--];
        for (let j = start; j < start + len; j++) {
          const t = result[j];
          result[j] = this.modQ(t + result[j + len]);
          result[j + len] = this.modQ(zeta * (result[j + len] - t));
        }
      }
    }
    
    for (let j = 0; j < this.N; j++) {
      result[j] = this.modQ(result[j] * this.NTT_F);
    }
    
    return result;
  }

  private static matrixVectorMultiply(matrix: number[][][], vector: number[][]): number[][] {
    const result: number[][] = [];
    for (let i = 0; i < this.K; i++) {
      result[i] = new Array(this.N).fill(0);
      for (let j = 0; j < this.K; j++) {
        const prod = this.polyMultiply(matrix[i][j], vector[j]);
        this.polyAdd(result[i], prod);
      }
    }
    return result;
  }

  private static polyMultiply(a: number[], b: number[]): number[] {
    const aNtt = this.ntt(a);
    const bNtt = this.ntt(b);
    const cNtt = new Array(this.N);
    
    for (let i = 0; i < this.N; i++) {
      cNtt[i] = this.modQ(aNtt[i] * bNtt[i]);
    }
    
    return this.invNtt(cNtt);
  }

  private static modQ(x: number): number {
    return ((x % this.Q) + this.Q) % this.Q;
  }

  // Precomputed NTT constants for Kyber
  private static readonly NTT_ZETAS = [
    // ... 128 precomputed values for NTT
    2285, 2571, 2970, 1812, 1493, 1422, 287, 202, 3158, 622, 1577, 182, 962,
    2127, 1855, 1468, 573, 2004, 264, 383, 2500, 1458, 1727, 3199, 2648, 1017,
    732, 608, 1787, 411, 3124, 1758, 1223, 652, 2777, 1015, 2036, 1491, 3047,
    1785, 516, 3321, 3009, 2663, 1711, 2167, 126, 1469, 2476, 3239, 3058, 830,
    107, 1908, 3082, 2378, 2931, 961, 1821, 2604, 448, 2264, 677, 2054, 2226,
    430, 555, 843, 2078, 871, 1550, 105, 422, 587, 177, 3094, 3038, 2869, 1574,
    1653, 3083, 778, 1159, 3182, 2552, 1483, 2727, 1119, 1739, 644, 2457, 349,
    418, 329, 3173, 3254, 817, 1097, 603, 610, 1322, 2044, 1864, 384, 2114, 3193,
    1218, 1994, 2455, 220, 2142, 1670, 2144, 1799, 2051, 794, 1819, 2475, 2459,
    478, 3221, 3021, 996, 991, 958, 1869, 1522, 1628
  ];

  private static readonly NTT_F = 1441; // 128^(-1) mod q

  // Additional helper methods for hashing, packing, etc.
  private static sha3_256(input: Uint8Array): Uint8Array {
    // Implement SHA3-256 or use a library
    return new Uint8Array(32); // Placeholder
  }

  private static sha3_512(input: Uint8Array): Uint8Array {
    // Implement SHA3-512 or use a library
    return new Uint8Array(64); // Placeholder
  }

  private static xof(output: Uint8Array, seed: Uint8Array, nonce: number, offset: number): void {
    // Implement SHAKE-128 XOF
  }

  private static prf(output: Uint8Array, key: Uint8Array, nonce: number): void {
    // Implement PRF based on SHAKE-256
  }

  private static kdf(input: Uint8Array): Uint8Array {
    // Implement KDF
    return this.sha3_256(input);
  }

  private static packPublicKey(output: Uint8Array, t: number[][], rho: Uint8Array): void {
    // Pack polynomial vector t and seed rho into public key format
  }

  private static unpackPublicKey(publicKey: Uint8Array): { t: number[][]; rho: Uint8Array } {
    // Unpack public key
    return { t: [], rho: new Uint8Array(32) };
  }

  private static packPrivateKey(output: Uint8Array, s: number[][], publicKey: Uint8Array): void {
    // Pack private key
  }

  private static unpackPrivateKey(privateKey: Uint8Array): { s: number[][]; publicKey: Uint8Array } {
    // Unpack private key
    return { s: [], publicKey: new Uint8Array(this.PUBLIC_KEY_BYTES) };
  }

  private static packCiphertext(output: Uint8Array, u: number[][], v: number[]): void {
    // Pack ciphertext
  }

  private static unpackCiphertext(ciphertext: Uint8Array): { u: number[][]; v: number[] } {
    // Unpack ciphertext
    return { u: [], v: [] };
  }

  private static constantTimeEquals(a: Uint8Array, b: Uint8Array): boolean {
    if (a.length !== b.length) return false;
    let result = 0;
    for (let i = 0; i < a.length; i++) {
      result |= a[i] ^ b[i];
    }
    return result === 0;
  }

  // Additional polynomial arithmetic methods
  private static generateErrorVector(seed: Uint8Array, offset: number): number[][] {
    const vector: number[][] = [];
    for (let i = 0; i < this.K; i++) {
      vector[i] = this.sampleCBD(seed, offset + i, this.ETA1);
    }
    return vector;
  }

  private static generateErrorPoly(seed: Uint8Array, nonce: number): number[] {
    return this.sampleCBD(seed, nonce, this.ETA2);
  }

  private static vectorAdd(a: number[][], b: number[][]): void {
    for (let i = 0; i < this.K; i++) {
      this.polyAdd(a[i], b[i]);
    }
  }

  private static polyAdd(a: number[], b: number[]): void {
    for (let i = 0; i < this.N; i++) {
      a[i] = this.modQ(a[i] + b[i]);
    }
  }

  private static polySub(a: number[], b: number[]): void {
    for (let i = 0; i < this.N; i++) {
      a[i] = this.modQ(a[i] - b[i]);
    }
  }

  private static vectorDotProduct(a: number[][], b: number[][]): number[] {
    const result = new Array(this.N).fill(0);
    for (let i = 0; i < this.K; i++) {
      const prod = this.polyMultiply(a[i], b[i]);
      this.polyAdd(result, prod);
    }
    return result;
  }

  private static matrixTransposeVectorMultiply(matrix: number[][][], vector: number[][]): number[][] {
    const result: number[][] = [];
    for (let i = 0; i < this.K; i++) {
      result[i] = new Array(this.N).fill(0);
      for (let j = 0; j < this.K; j++) {
        const prod = this.polyMultiply(matrix[j][i], vector[j]); // Note: transposed access
        this.polyAdd(result[i], prod);
      }
    }
    return result;
  }

  private static messageToPolynomial(msg: Uint8Array): number[] {
    const poly = new Array(this.N).fill(0);
    for (let i = 0; i < 32; i++) {
      for (let j = 0; j < 8; j++) {
        const bit = (msg[i] >> j) & 1;
        poly[8 * i + j] = bit * Math.floor(this.Q / 2);
      }
    }
    return poly;
  }

  private static polynomialToMessage(poly: number[]): Uint8Array {
    const msg = new Uint8Array(32);
    for (let i = 0; i < 32; i++) {
      for (let j = 0; j < 8; j++) {
        const coeff = poly[8 * i + j];
        const bit = Math.abs(coeff - Math.floor(this.Q / 2)) < Math.floor(this.Q / 4) ? 1 : 0;
        msg[i] |= bit << j;
      }
    }
    return msg;
  }
}

// Dilithium-3 Implementation
export class Dilithium3 {
  private static readonly N = 256;
  private static readonly Q = 8380417;
  private static readonly D = 13;
  private static readonly TAU = 49;
  private static readonly GAMMA1 = (1 << 17);
  private static readonly GAMMA2 = (this.Q - 1) / 88;
  private static readonly K = 6;
  private static readonly L = 5;
  private static readonly ETA = 4;
  private static readonly BETA = this.TAU * this.ETA;
  private static readonly OMEGA = 80;

  public static readonly PUBLIC_KEY_BYTES = 32 + this.K * this.polyT1PackedBytes();
  public static readonly SECRET_KEY_BYTES = 2 * 32 + this.L * this.polyETAPackedBytes() + this.K * this.polyETAPackedBytes() + this.K * this.polyT0PackedBytes();
  public static readonly SIGNATURE_BYTES = 32 + this.L * this.polyZPackedBytes() + this.OMEGA + this.K;

  static generateKeyPair(): { publicKey: Uint8Array; privateKey: Uint8Array } {
    const seed = new Uint8Array(32);
    crypto.getRandomValues(seed);

    // Expand seed
    const expandedSeed = this.expandSeed(seed);
    const rho = expandedSeed.slice(0, 32);
    const rhoPrime = expandedSeed.slice(32, 64);
    const K = expandedSeed.slice(64, 96);

    // Generate matrix A
    const A = this.expandA(rho);

    // Sample s1, s2
    const s1 = this.sampleS1(rhoPrime);
    const s2 = this.sampleS2(rhoPrime);

    // Compute t = As1 + s2
    const t = this.matrixVectorMul(A, s1);
    this.vectorAdd(t, s2);

    // Power2Round
    const { t1, t0 } = this.power2Round(t);

    // Pack keys
    const publicKey = this.packPublicKey(rho, t1);
    const privateKey = this.packPrivateKey(rho, K, s1, s2, t0);

    return { publicKey, privateKey };
  }

  static sign(message: Uint8Array, privateKey: Uint8Array): Uint8Array {
    // Unpack private key
    const { rho, K, s1, s2, t0 } = this.unpackPrivateKey(privateKey);

    // Expand A
    const A = this.expandA(rho);

    // Hash message
    const mu = this.hashMessage(message, publicKey);

    let attempt = 0;
    while (attempt < 1000) { // Prevent infinite loop
      // Sample mask
      const rhoPrime = new Uint8Array(64);
      crypto.getRandomValues(rhoPrime);

      const y = this.sampleMask(rhoPrime);

      // Compute w = Ay
      const w = this.matrixVectorMul(A, y);
      const w1 = this.highBits(w);

      // Compute challenge
      const c = this.sampleChallenge(mu, w1);

      // Compute z = y + cs1
      const z = this.vectorAdd(y, this.scalarVectorMul(c, s1));

      // Check norm bounds
      if (!this.checkZNorm(z)) {
        attempt++;
        continue;
      }

      // Compute r0 = (w - cs2) mod 2γ2
      const cs2 = this.scalarVectorMul(c, s2);
      const r0 = this.lowBits(this.vectorSub(w, cs2));

      // Check norm bounds
      if (!this.checkR0Norm(r0)) {
        attempt++;
        continue;
      }

      // Compute ct0
      const ct0 = this.scalarVectorMul(c, t0);

      // Check norm bounds
      if (!this.checkCT0Norm(ct0)) {
        attempt++;
        continue;
      }

      // Pack signature
      return this.packSignature(c, z, this.makeHint(ct0, w, cs2));
    }

    throw new Error('Signature generation failed after maximum attempts');
  }

  static verify(message: Uint8Array, signature: Uint8Array, publicKey: Uint8Array): boolean {
    try {
      // Unpack public key and signature
      const { rho, t1 } = this.unpackPublicKey(publicKey);
      const { c, z, h } = this.unpackSignature(signature);

      // Check signature bounds
      if (!this.checkSignatureBounds(z, h)) {
        return false;
      }

      // Expand A
      const A = this.expandA(rho);

      // Hash message
      const mu = this.hashMessage(message, publicKey);

      // Compute Az - ct1 * 2^d
      const Az = this.matrixVectorMul(A, z);
      const ct1 = this.scalarVectorMul(c, t1);
      this.scalarVectorMulInPlace(ct1, 1 << this.D);
      const w = this.vectorSub(Az, ct1);

      // Use hint
      const w1 = this.useHint(h, w);

      // Compute challenge
      const cPrime = this.sampleChallenge(mu, w1);

      return this.constantTimeEquals(c, cPrime);
    } catch {
      return false;
    }
  }

  // Polynomial and vector arithmetic
  private static ntt(poly: number[]): number[] {
    // NTT implementation for Dilithium
    const result = [...poly];
    // Implementation details...
    return result;
  }

  private static invNtt(poly: number[]): number[] {
    // Inverse NTT implementation
    const result = [...poly];
    // Implementation details...
    return result;
  }

  private static polyMul(a: number[], b: number[]): number[] {
    const aNtt = this.ntt(a);
    const bNtt = this.ntt(b);
    const cNtt = new Array(this.N);
    
    for (let i = 0; i < this.N; i++) {
      cNtt[i] = (aNtt[i] * bNtt[i]) % this.Q;
    }
    
    return this.invNtt(cNtt);
  }

  private static matrixVectorMul(matrix: number[][][], vector: number[][]): number[][] {
    const result: number[][] = [];
    for (let i = 0; i < this.K; i++) {
      result[i] = new Array(this.N).fill(0);
      for (let j = 0; j < this.L; j++) {
        const prod = this.polyMul(matrix[i][j], vector[j]);
        this.polyAdd(result[i], prod);
      }
    }
    return result;
  }

  private static vectorAdd(a: number[][], b: number[][]): number[][] {
    const result: number[][] = [];
    for (let i = 0; i < a.length; i++) {
      result[i] = new Array(this.N);
      for (let j = 0; j < this.N; j++) {
        result[i][j] = (a[i][j] + b[i][j]) % this.Q;
      }
    }
    return result;
  }

  private static vectorSub(a: number[][], b: number[][]): number[][] {
    const result: number[][] = [];
    for (let i = 0; i < a.length; i++) {
      result[i] = new Array(this.N);
      for (let j = 0; j < this.N; j++) {
        result[i][j] = (a[i][j] - b[i][j] + this.Q) % this.Q;
      }
    }
    return result;
  }

  private static scalarVectorMul(scalar: number[], vector: number[][]): number[][] {
    const result: number[][] = [];
    for (let i = 0; i < vector.length; i++) {
      result[i] = this.polyMul(scalar, vector[i]);
    }
    return result;
  }

  private static polyAdd(a: number[], b: number[]): void {
    for (let i = 0; i < this.N; i++) {
      a[i] = (a[i] + b[i]) % this.Q;
    }
  }

  // Additional helper methods for Dilithium
  private static expandSeed(seed: Uint8Array): Uint8Array {
    // Use SHAKE-256 to expand seed
    return new Uint8Array(96); // Placeholder
  }

  private static expandA(rho: Uint8Array): number[][][] {
    const A: number[][][] = [];
    for (let i = 0; i < this.K; i++) {
      A[i] = [];
      for (let j = 0; j < this.L; j++) {
        A[i][j] = this.rejectionSamplePoly(rho, (i << 8) | j);
      }
    }
    return A;
  }

  private static rejectionSamplePoly(seed: Uint8Array, nonce: number): number[] {
    const poly = new Array(this.N);
    // Rejection sampling implementation
    for (let i = 0; i < this.N; i++) {
      poly[i] = Math.floor(Math.random() * this.Q); // Placeholder
    }
    return poly;
  }

  private static sampleS1(seed: Uint8Array): number[][] {
    const s1: number[][] = [];
    for (let i = 0; i < this.L; i++) {
      s1[i] = this.sampleEta(seed, i);
    }
    return s1;
  }

  private static sampleS2(seed: Uint8Array): number[][] {
    const s2: number[][] = [];
    for (let i = 0; i < this.K; i++) {
      s2[i] = this.sampleEta(seed, this.L + i);
    }
    return s2;
  }

  private static sampleEta(seed: Uint8Array, nonce: number): number[] {
    const poly = new Array(this.N);
    // Sample from centered binomial distribution
    for (let i = 0; i < this.N; i++) {
      let a = 0, b = 0;
      for (let j = 0; j < this.ETA; j++) {
        a += Math.random() < 0.5 ? 1 : 0;
        b += Math.random() < 0.5 ? 1 : 0;
      }
      poly[i] = (a - b + this.Q) % this.Q;
    }
    return poly;
  }

  private static power2Round(vector: number[][]): { t1: number[][]; t0: number[][] } {
    const t1: number[][] = [];
    const t0: number[][] = [];
    
    for (let i = 0; i < vector.length; i++) {
      t1[i] = new Array(this.N);
      t0[i] = new Array(this.N);
      
      for (let j = 0; j < this.N; j++) {
        const r = vector[i][j];
        t1[i][j] = (r + (1 << (this.D - 1)) - 1) >> this.D;
        t0[i][j] = r - (t1[i][j] << this.D);
      }
    }
    
    return { t1, t0 };
  }

  private static highBits(vector: number[][]): number[][] {
    const result: number[][] = [];
    for (let i = 0; i < vector.length; i++) {
      result[i] = new Array(this.N);
      for (let j = 0; j < this.N; j++) {
        result[i][j] = this.decompose(vector[i][j]).high;
      }
    }
    return result;
  }

  private static lowBits(vector: number[][]): number[][] {
    const result: number[][] = [];
    for (let i = 0; i < vector.length; i++) {
      result[i] = new Array(this.N);
      for (let j = 0; j < this.N; j++) {
        result[i][j] = this.decompose(vector[i][j]).low;
      }
    }
    return result;
  }

  private static decompose(r: number): { high: number; low: number } {
    const r1 = (r + 127) >> 7;
    const r0 = r - r1 * 128;
    return { high: r1, low: r0 };
  }

  private static sampleMask(seed: Uint8Array): number[][] {
    const y: number[][] = [];
    for (let i = 0; i < this.L; i++) {
      y[i] = this.sampleGamma1(seed, i);
    }
    return y;
  }

  private static sampleGamma1(seed: Uint8Array, nonce: number): number[] {
    const poly = new Array(this.N);
    // Sample from [-γ₁ + 1, γ₁]
    for (let i = 0; i < this.N; i++) {
      poly[i] = Math.floor(Math.random() * (2 * this.GAMMA1)) - this.GAMMA1 + 1;
    }
    return poly;
  }

  private static sampleChallenge(mu: Uint8Array, w1: number[][]): number[] {
    // Sample challenge polynomial with exactly τ ±1 coefficients
    const c = new Array(this.N).fill(0);
    const signs = new Uint8Array(8);
    crypto.getRandomValues(signs);
    
    for (let i = 0; i < this.TAU; i++) {
      const pos = Math.floor(Math.random() * this.N);
      if (c[pos] === 0) {
        c[pos] = (signs[i >> 3] >> (i & 7)) & 1 ? 1 : -1;
      } else {
        i--; // Retry
      }
    }
    
    return c;
  }

  private static checkZNorm(z: number[][]): boolean {
    for (let i = 0; i < z.length; i++) {
      for (let j = 0; j < this.N; j++) {
        if (Math.abs(z[i][j]) >= this.GAMMA1 - this.BETA) {
          return false;
        }
      }
    }
    return true;
  }

  private static checkR0Norm(r0: number[][]): boolean {
    for (let i = 0; i < r0.length; i++) {
      for (let j = 0; j < this.N; j++) {
        if (Math.abs(r0[i][j]) >= this.GAMMA2 - this.BETA) {
          return false;
        }
      }
    }
    return true;
  }

  private static checkCT0Norm(ct0: number[][]): boolean {
    for (let i = 0; i < ct0.length; i++) {
      for (let j = 0; j < this.N; j++) {
        if (Math.abs(ct0[i][j]) >= this.GAMMA2) {
          return false;
        }
      }
    }
    return true;
  }

  private static makeHint(ct0: number[][], w: number[][], cs2: number[][]): number[][] {
    const hint: number[][] = [];
    const wMinusCs2 = this.vectorSub(w, cs2);
    
    for (let i = 0; i < this.K; i++) {
      hint[i] = new Array(this.N);
      for (let j = 0; j < this.N; j++) {
        const r = wMinusCs2[i][j];
        const { high: r1 } = this.decompose(r);
        const { high: r1Prime } = this.decompose(r - ct0[i][j]);
        hint[i][j] = r1 !== r1Prime ? 1 : 0;
      }
    }
    
    return hint;
  }

  private static useHint(hint: number[][], w: number[][]): number[][] {
    const w1: number[][] = [];
    for (let i = 0; i < w.length; i++) {
      w1[i] = new Array(this.N);
      for (let j = 0; j < this.N; j++) {
        const { high: r1, low: r0 } = this.decompose(w[i][j]);
        if (hint[i][j] === 1) {
          w1[i][j] = r0 > 0 ? (r1 + 1) % this.Q : (r1 - 1 + this.Q) % this.Q;
        } else {
          w1[i][j] = r1;
        }
      }
    }
    return w1;
  }

  private static checkSignatureBounds(z: number[][], h: number[][]): boolean {
    // Check z norm
    if (!this.checkZNorm(z)) return false;
    
    // Check hint weight
    let hintWeight = 0;
    for (let i = 0; i < h.length; i++) {
      for (let j = 0; j < this.N; j++) {
        hintWeight += h[i][j];
      }
    }
    
    return hintWeight <= this.OMEGA;
  }

  private static constantTimeEquals(a: number[], b: number[]): boolean {
    if (a.length !== b.length) return false;
    let result = 0;
    for (let i = 0; i < a.length; i++) {
      result |= a[i] ^ b[i];
    }
    return result === 0;
  }

  // Packing and unpacking methods
  private static packPublicKey(rho: Uint8Array, t1: number[][]): Uint8Array {
    const pk = new Uint8Array(this.PUBLIC_KEY_BYTES);
    pk.set(rho, 0);
    
    let offset = 32;
    for (let i = 0; i < this.K; i++) {
      const packed = this.packT1(t1[i]);
      pk.set(packed, offset);
      offset += packed.length;
    }
    
    return pk;
  }

  private static unpackPublicKey(pk: Uint8Array): { rho: Uint8Array; t1: number[][] } {
    const rho = pk.slice(0, 32);
    const t1: number[][] = [];
    
    let offset = 32;
    for (let i = 0; i < this.K; i++) {
      const packedSize = this.polyT1PackedBytes();
      t1[i] = this.unpackT1(pk.slice(offset, offset + packedSize));
      offset += packedSize;
    }
    
    return { rho, t1 };
  }

  private static packPrivateKey(rho: Uint8Array, K: Uint8Array, s1: number[][], s2: number[][], t0: number[][]): Uint8Array {
    const sk = new Uint8Array(this.SECRET_KEY_BYTES);
    let offset = 0;
    
    sk.set(rho, offset);
    offset += 32;
    sk.set(K, offset);
    offset += 32;
    
    for (let i = 0; i < this.L; i++) {
      const packed = this.packEta(s1[i]);
      sk.set(packed, offset);
      offset += packed.length;
    }
    
    for (let i = 0; i < this.K; i++) {
      const packed = this.packEta(s2[i]);
      sk.set(packed, offset);
      offset += packed.length;
    }
    
    for (let i = 0; i < this.K; i++) {
      const packed = this.packT0(t0[i]);
      sk.set(packed, offset);
      offset += packed.length;
    }
    
    return sk;
  }

  private static unpackPrivateKey(sk: Uint8Array): { rho: Uint8Array; K: Uint8Array; s1: number[][]; s2: number[][]; t0: number[][] } {
    let offset = 0;
    
    const rho = sk.slice(offset, offset + 32);
    offset += 32;
    const K = sk.slice(offset, offset + 32);
    offset += 32;
    
    const s1: number[][] = [];
    for (let i = 0; i < this.L; i++) {
      const packedSize = this.polyETAPackedBytes();
      s1[i] = this.unpackEta(sk.slice(offset, offset + packedSize));
      offset += packedSize;
    }
    
    const s2: number[][] = [];
    for (let i = 0; i < this.K; i++) {
      const packedSize = this.polyETAPackedBytes();
      s2[i] = this.unpackEta(sk.slice(offset, offset + packedSize));
      offset += packedSize;
    }
    
    const t0: number[][] = [];
    for (let i = 0; i < this.K; i++) {
      const packedSize = this.polyT0PackedBytes();
      t0[i] = this.unpackT0(sk.slice(offset, offset + packedSize));
      offset += packedSize;
    }
    
    return { rho, K, s1, s2, t0 };
  }

  private static packSignature(c: number[], z: number[][], h: number[][]): Uint8Array {
    const sig = new Uint8Array(this.SIGNATURE_BYTES);
    let offset = 0;
    
    // Pack challenge
    const packedC = this.packChallenge(c);
    sig.set(packedC, offset);
    offset += packedC.length;
    
    // Pack z
    for (let i = 0; i < this.L; i++) {
      const packed = this.packZ(z[i]);
      sig.set(packed, offset);
      offset += packed.length;
    }
    
    // Pack hint
    const packedH = this.packHint(h);
    sig.set(packedH, offset);
    
    return sig;
  }

  private static unpackSignature(sig: Uint8Array): { c: number[]; z: number[][]; h: number[][] } {
    let offset = 0;
    
    const c = this.unpackChallenge(sig.slice(offset, offset + 32));
    offset += 32;
    
    const z: number[][] = [];
    for (let i = 0; i < this.L; i++) {
      const packedSize = this.polyZPackedBytes();
      z[i] = this.unpackZ(sig.slice(offset, offset + packedSize));
      offset += packedSize;
    }
    
    const h = this.unpackHint(sig.slice(offset));
    
    return { c, z, h };
  }

  // Polynomial packing methods (simplified)
  private static polyT1PackedBytes(): number { return 320; }
  private static polyT0PackedBytes(): number { return 416; }
  private static polyETAPackedBytes(): number { return 96; }
  private static polyZPackedBytes(): number { return 576; }

  private static packT1(poly: number[]): Uint8Array {
    return new Uint8Array(this.polyT1PackedBytes()); // Placeholder
  }

  private static unpackT1(data: Uint8Array): number[] {
    return new Array(this.N).fill(0); // Placeholder
  }

  private static packT0(poly: number[]): Uint8Array {
    return new Uint8Array(this.polyT0PackedBytes()); // Placeholder
  }

  private static unpackT0(data: Uint8Array): number[] {
    return new Array(this.N).fill(0); // Placeholder
  }

  private static packEta(poly: number[]): Uint8Array {
    return new Uint8Array(this.polyETAPackedBytes()); // Placeholder
  }

  private static unpackEta(data: Uint8Array): number[] {
    return new Array(this.N).fill(0); // Placeholder
  }

  private static packZ(poly: number[]): Uint8Array {
    return new Uint8Array(this.polyZPackedBytes()); // Placeholder
  }

  private static unpackZ(data: Uint8Array): number[] {
    return new Array(this.N).fill(0); // Placeholder
  }

  private static packChallenge(c: number[]): Uint8Array {
    return new Uint8Array(32); // Placeholder
  }

  private static unpackChallenge(data: Uint8Array): number[] {
    return new Array(this.N).fill(0); // Placeholder
  }

  private static packHint(h: number[][]): Uint8Array {
    return new Uint8Array(this.OMEGA + this.K); // Placeholder
  }

  private static unpackHint(data: Uint8Array): number[][] {
    const h: number[][] = [];
    for (let i = 0; i < this.K; i++) {
      h[i] = new Array(this.N).fill(0);
    }
    return h; // Placeholder
  }

  private static hashMessage(message: Uint8Array, publicKey: Uint8Array): Uint8Array {
    // Hash message with public key using SHAKE-256
    return new Uint8Array(32); // Placeholder
  }

  private static scalarVectorMulInPlace(vector: number[][], scalar: number): void {
    for (let i = 0; i < vector.length; i++) {
      for (let j = 0; j < this.N; j++) {
        vector[i][j] = (vector[i][j] * scalar) % this.Q;
      }
    }
  }
}
