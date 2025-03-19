import { TreeNode, ValueType } from "./types";

// Types for the serialized POD format
export type RawValue = { Raw: string };
export type IntValue = { Int: string };
export type SetValue = { Set: SerializedValue[] };
export type DictionaryValue = { Dictionary: Record<string, SerializedValue> };
export type ArrayValue = SerializedValue[];

export type SerializedValue =
  | RawValue
  | IntValue
  | SetValue
  | DictionaryValue
  | ArrayValue
  | string
  | boolean;

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

// Convert the tree editor state to a CreateSignedPodRequest format
export function serializePodTree(nodes: TreeNode[]): {
  signer: string;
  key_values: Record<string, SerializedValue>;
} {
  const key_values: Record<string, SerializedValue> = {};

  nodes.forEach((node) => {
    const value = node.value;

    // Handle Set values
    if (node.type === ValueType.Set && value instanceof Set) {
      key_values[node.key] = { Set: Array.from(value) };
    }
    // Handle Dictionary values
    else if (
      node.type === ValueType.Dictionary &&
      value &&
      typeof value === "object" &&
      !Array.isArray(value)
    ) {
      key_values[node.key] = {
        Dictionary: value as Record<string, SerializedValue>
      };
    }
    // Handle Int values
    else if (node.type === ValueType.Int) {
      key_values[node.key] = { Int: value.toString() };
    }
    // Handle Raw values
    else if (node.type === ValueType.Raw) {
      key_values[node.key] = { Raw: value.toString() };
    }
    // Handle Array values
    else if (node.type === ValueType.Array) {
      key_values[node.key] = value as ArrayValue;
    }
    // Handle String values
    else if (node.type === ValueType.String) {
      key_values[node.key] = value as string;
    }
    // Handle Bool values
    else if (node.type === ValueType.Bool) {
      key_values[node.key] = value as boolean;
    }
    // Handle all other values directly
    else {
      key_values[node.key] = value as SerializedValue;
    }
  });

  return {
    signer: "example-signer",
    key_values
  };
}

// Convert a TreeNode to its serialized format
export function serializeValue(node: TreeNode): SerializedValue {
  switch (node.type) {
    case ValueType.String:
      return node.value as string;

    case ValueType.Int:
      return { Int: numberToString(node.value as string) };

    case ValueType.Bool:
      return node.value as boolean;

    case ValueType.Array:
      return (node.children || []).map((child: TreeNode) =>
        serializeValue(child)
      );

    case ValueType.Set: {
      const setValue = node.value as Set<SerializedValue>;
      const arrayValue = Array.from(setValue);
      return { Set: arrayValue };
    }

    case ValueType.Dictionary: {
      const dict: Record<string, SerializedValue> = {};
      node.children?.forEach((child: TreeNode) => {
        dict[child.key] = serializeValue(child);
      });
      return { Dictionary: dict };
    }

    case ValueType.Raw:
      return { Raw: node.value as string };

    default:
      throw new Error(`Unsupported node type: ${node.type}`);
  }
}

// Convert a SerializedValue to a TreeNode
export function deserializeValue(
  value: SerializedValue,
  key: string = ""
): TreeNode {
  if (typeof value === "string") {
    return {
      id: crypto.randomUUID(),
      key,
      type: ValueType.String,
      value
    };
  } else if (typeof value === "boolean") {
    return {
      id: crypto.randomUUID(),
      key,
      type: ValueType.Bool,
      value
    };
  } else if ("Int" in value) {
    return {
      id: crypto.randomUUID(),
      key,
      type: ValueType.Int,
      value: value.Int
    };
  } else if ("Raw" in value) {
    return {
      id: crypto.randomUUID(),
      key,
      type: ValueType.Raw,
      value: value.Raw
    };
  } else if ("Set" in value) {
    return {
      id: crypto.randomUUID(),
      key,
      type: ValueType.Set,
      value: new Set(value.Set),
      children: value.Set.map((v, i) => deserializeValue(v, `item${i}`))
    };
  } else if ("Dictionary" in value) {
    return {
      id: crypto.randomUUID(),
      key,
      type: ValueType.Dictionary,
      value: {},
      children: Object.entries(value.Dictionary).map(([k, v]) =>
        deserializeValue(v, k)
      )
    };
  } else if (Array.isArray(value)) {
    return {
      id: crypto.randomUUID(),
      key,
      type: ValueType.Array,
      value: [],
      children: value.map((v, i) => deserializeValue(v, `item${i}`))
    };
  }
  throw new Error(`Unsupported value type: ${typeof value}`);
}
