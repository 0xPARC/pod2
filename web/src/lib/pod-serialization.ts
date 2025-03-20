// Constants for i64 limits in Rust
const I64_MIN = -9223372036854775808n;
const I64_MAX = 9223372036854775807n;

// Helper function to convert a number to a string representation
// This handles large integers that need to be preserved exactly
// Throws an error if the number is outside i64 bounds
export function numberToString(n: number | string): string {
  try {
    // Convert to BigInt to preserve precision
    const bigIntValue =
      typeof n === "string" ? BigInt(n) : BigInt(Math.floor(n));

    // Validate against i64 bounds
    if (bigIntValue < I64_MIN || bigIntValue > I64_MAX) {
      throw new Error(`Integer value ${bigIntValue} is outside of i64 bounds`);
    }

    return bigIntValue.toString();
  } catch (err) {
    if (err instanceof Error && err.message.includes("i64 bounds")) {
      throw err;
    }
    throw new Error(`Invalid integer value: ${n}`);
  }
}
