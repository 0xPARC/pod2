import type { Value } from "@/types/pod2";
import { uint8ArrayToHex } from "uint8array-extras";

export function serialize(value: unknown): Value {
  if (typeof value === "string") {
    return value;
  }

  if (typeof value === "bigint") {
    return { Int: value.toString() };
  }

  if (typeof value === "boolean") {
    return value;
  }

  if (Array.isArray(value)) {
    return value.map(serialize);
  }

  if (typeof value === "object" && value !== null) {
    return {
      Dictionary: Object.fromEntries(
        Object.entries(value).map(([key, value]) => [key, serialize(value)])
      ),
    };
  }

  if (value instanceof Set) {
    return {
      Set: Array.from(value).map(serialize),
    };
  }

  if (value instanceof Uint8Array) {
    return { Raw: uint8ArrayToHex(value) };
  }

  throw new Error(`Unknown value type: ${typeof value}`);
}
