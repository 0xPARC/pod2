import { describe, it, expect } from "vitest";
import {
  numberToString,
  serializeValue,
  deserializeValue,
  serializePodTree
} from "./pod-serialization";
import { TreeNode, ValueType } from "./types";

describe("pod-serialization", () => {
  describe("numberToString", () => {
    it("should handle valid integers", () => {
      expect(numberToString(42)).toBe("42");
      expect(numberToString(-42)).toBe("-42");
      expect(numberToString("42")).toBe("42");
      expect(numberToString("-42")).toBe("-42");
    });

    it("should handle large integers within bounds", () => {
      expect(numberToString("9223372036854775807")).toBe("9223372036854775807");
      expect(numberToString("-9223372036854775808")).toBe(
        "-9223372036854775808"
      );
    });

    it("should throw error for non-integer numbers", () => {
      expect(() => numberToString(42.5)).toThrow("Invalid integer value: 42.5");
      expect(() => numberToString("42.5")).toThrow(
        "Invalid integer value: 42.5"
      );
    });

    it("should throw error for integers outside i64 bounds", () => {
      expect(() => numberToString("9223372036854775808")).toThrow(
        "Integer value 9223372036854775808 is outside of i64 bounds"
      );
      expect(() => numberToString("-9223372036854775809")).toThrow(
        "Integer value -9223372036854775809 is outside of i64 bounds"
      );
    });
  });

  describe("serializeValue", () => {
    it("should serialize primitive values", () => {
      const stringNode: TreeNode = {
        id: "1",
        key: "str",
        type: ValueType.String,
        value: "hello"
      };
      expect(serializeValue(stringNode)).toBe("hello");

      const intNode: TreeNode = {
        id: "2",
        key: "num",
        type: ValueType.Int,
        value: "42"
      };
      expect(serializeValue(intNode)).toEqual({ Int: "42" });

      const boolNode: TreeNode = {
        id: "3",
        key: "bool",
        type: ValueType.Bool,
        value: true
      };
      expect(serializeValue(boolNode)).toBe(true);
    });

    it("should serialize array values", () => {
      const arrayNode: TreeNode = {
        id: "1",
        key: "arr",
        type: ValueType.Array,
        value: [],
        children: [
          {
            id: "2",
            key: "",
            type: ValueType.String,
            value: "hello"
          },
          {
            id: "3",
            key: "",
            type: ValueType.Int,
            value: "42"
          }
        ]
      };
      expect(serializeValue(arrayNode)).toEqual(["hello", { Int: "42" }]);
    });

    it("should serialize set values", () => {
      const setNode: TreeNode = {
        id: "1",
        key: "set",
        type: ValueType.Set,
        value: [],
        children: [
          {
            id: "2",
            key: "",
            type: ValueType.String,
            value: "hello"
          },
          {
            id: "3",
            key: "",
            type: ValueType.String,
            value: "42"
          }
        ]
      };
      expect(serializeValue(setNode)).toEqual({ Set: ["hello", "42"] });
    });

    it("should serialize dictionary values", () => {
      const dictNode: TreeNode = {
        id: "1",
        key: "dict",
        type: ValueType.Dictionary,
        value: {},
        children: [
          {
            id: "2",
            key: "str",
            type: ValueType.String,
            value: "hello"
          },
          {
            id: "3",
            key: "num",
            type: ValueType.Int,
            value: "42"
          }
        ]
      };
      expect(serializeValue(dictNode)).toEqual({
        Dictionary: {
          str: "hello",
          num: { Int: "42" }
        }
      });
    });
  });

  describe("deserializeValue", () => {
    it("should deserialize primitive values", () => {
      const stringNode = deserializeValue("hello", "str");
      expect(stringNode).toEqual({
        id: expect.any(String),
        key: "str",
        type: ValueType.String,
        value: "hello"
      });

      const intNode = deserializeValue({ Int: "42" }, "num");
      expect(intNode).toEqual({
        id: expect.any(String),
        key: "num",
        type: ValueType.Int,
        value: "42"
      });

      const boolNode = deserializeValue(true, "bool");
      expect(boolNode).toEqual({
        id: expect.any(String),
        key: "bool",
        type: ValueType.Bool,
        value: true
      });
    });

    it("should deserialize array values", () => {
      const arrayNode = deserializeValue(["hello", { Int: "42" }], "arr");
      expect(arrayNode).toEqual({
        id: expect.any(String),
        key: "arr",
        type: ValueType.Array,
        value: [],
        children: [
          {
            id: expect.any(String),
            key: "item0",
            type: ValueType.String,
            value: "hello"
          },
          {
            id: expect.any(String),
            key: "item1",
            type: ValueType.Int,
            value: "42"
          }
        ]
      });
    });

    it("should deserialize set values", () => {
      const setNode = deserializeValue({ Set: ["hello", "42"] }, "set");
      expect(setNode).toEqual({
        id: expect.any(String),
        key: "set",
        type: ValueType.Set,
        value: new Set(["hello", "42"]),
        children: [
          {
            id: expect.any(String),
            key: "item0",
            type: ValueType.String,
            value: "hello"
          },
          {
            id: expect.any(String),
            key: "item1",
            type: ValueType.String,
            value: "42"
          }
        ]
      });
    });

    it("should deserialize dictionary values", () => {
      const dictNode = deserializeValue(
        {
          Dictionary: {
            str: "hello",
            num: { Int: "42" }
          }
        },
        "dict"
      );
      expect(dictNode).toEqual({
        id: expect.any(String),
        key: "dict",
        type: ValueType.Dictionary,
        value: {},
        children: [
          {
            id: expect.any(String),
            key: "str",
            type: ValueType.String,
            value: "hello"
          },
          {
            id: expect.any(String),
            key: "num",
            type: ValueType.Int,
            value: "42"
          }
        ]
      });
    });
  });

  describe("serializePodTree", () => {
    it("should serialize string values", () => {
      const nodes: TreeNode[] = [
        {
          id: "1",
          key: "string",
          type: ValueType.String,
          value: "hello"
        }
      ];

      const result = serializePodTree(nodes);
      expect(result.key_values.string).toBe("hello");
    });

    it("should serialize integer values", () => {
      const nodes: TreeNode[] = [
        {
          id: "1",
          key: "integer",
          type: ValueType.Int,
          value: "42"
        }
      ];

      const result = serializePodTree(nodes);
      expect(result.key_values.integer).toEqual({ Int: "42" });
    });

    it("should serialize boolean values", () => {
      const nodes: TreeNode[] = [
        {
          id: "1",
          key: "boolean",
          type: ValueType.Bool,
          value: true
        }
      ];

      const result = serializePodTree(nodes);
      expect(result.key_values.boolean).toBe(true);
    });

    it("should serialize array values", () => {
      const nodes: TreeNode[] = [
        {
          id: "1",
          key: "array",
          type: ValueType.Array,
          value: ["hello", "42"]
        }
      ];

      const result = serializePodTree(nodes);
      expect(result.key_values.array).toEqual(["hello", "42"]);
    });

    it("should serialize set values", () => {
      const nodes: TreeNode[] = [
        {
          id: "1",
          key: "set",
          type: ValueType.Set,
          value: new Set(["hello", "42"])
        }
      ];

      const result = serializePodTree(nodes);
      expect(result.key_values.set).toEqual({ Set: ["hello", "42"] });
    });

    it("should serialize dictionary values", () => {
      const nodes: TreeNode[] = [
        {
          id: "1",
          key: "dictionary",
          type: ValueType.Dictionary,
          value: { a: "hello", b: "42" }
        }
      ];

      const result = serializePodTree(nodes);
      expect(result.key_values.dictionary).toEqual({
        Dictionary: { a: "hello", b: "42" }
      });
    });

    it("should serialize raw values", () => {
      const nodes: TreeNode[] = [
        {
          id: "1",
          key: "raw",
          type: ValueType.Raw,
          value: "0x1234"
        }
      ];

      const result = serializePodTree(nodes);
      expect(result.key_values.raw).toEqual({ Raw: "0x1234" });
    });

    it("should serialize nested values", () => {
      const nodes: TreeNode[] = [
        {
          id: "1",
          key: "nested",
          type: ValueType.Dictionary,
          value: {},
          children: [
            {
              id: "2",
              key: "string",
              type: ValueType.String,
              value: "hello"
            },
            {
              id: "3",
              key: "integer",
              type: ValueType.Int,
              value: "42"
            },
            {
              id: "4",
              key: "boolean",
              type: ValueType.Bool,
              value: true
            },
            {
              id: "5",
              key: "array",
              type: ValueType.Array,
              value: [],
              children: [
                {
                  id: "6",
                  key: "item0",
                  type: ValueType.String,
                  value: "a"
                },
                {
                  id: "7",
                  key: "item1",
                  type: ValueType.String,
                  value: "b"
                }
              ]
            },
            {
              id: "8",
              key: "dictionary",
              type: ValueType.Dictionary,
              value: {},
              children: [
                {
                  id: "9",
                  key: "key",
                  type: ValueType.String,
                  value: "value"
                }
              ]
            }
          ]
        }
      ];

      const result = serializePodTree(nodes);
      expect(result.key_values.nested).toEqual({
        Dictionary: {
          string: "hello",
          integer: { Int: "42" },
          boolean: true,
          array: ["a", "b"],
          dictionary: { Dictionary: { key: "value" } }
        }
      });
    });
  });
});
