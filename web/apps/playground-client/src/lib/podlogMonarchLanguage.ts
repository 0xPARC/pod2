import type { languages } from "monaco-editor";

export const podlogMonarchLanguage = {
  // Set defaultToken to invalid to see if you do not cover all cases
  defaultToken: "invalid",

  keywords: [
    "REQUEST",
    "AND",
    "OR", // 'true', 'false', // Handled by specific literal rules now
    "ValueOf",
    "Equal",
    "NotEqual",
    "Gt",
    "GtEq",
    "Lt",
    "LtEq",
    "Contains",
    "NotContains",
    "SumOf",
    "ProductOf",
    "MaxOf",
    "HashOf",
    "DictContains",
    "DictNotContains",
    "ArrayContains",
    "SetContains",
    "SetNotContains",
    // Note: 'true' and 'false' are removed from here as they'll have specific rules
  ],

  operators: [
    "=", // Removed , : [ ] ( ) as they are handled by delimiter or bracket rules
    // '#[' and '#{' are not standard operators, might be part of a custom construct
  ],

  symbols: /[=,:(){}\\[\\]#?]+/, // Includes '?' for variables and '#'

  escapes:
    /\\\\(?:[abfnrtv\\"']|x[0-9A-Fa-f]{1,4}|u[0-9A-Fa-f]{4}|U[0-9A-Fa-f]{8})/,

  tokenizer: {
    root: [
      // Whitespace and comments
      { include: "@whitespace" },

      // Specific keywords with symbols or specific prefixes first
      [/private:/, "keyword"],

      // --- Literals ---
      // Boolean Literals (placed before general identifiers)
      [/\\b(true|false)\\b/, "constant.language.boolean.podlog"],

      // Number Literals
      [/0[xX][0-9a-fA-F]+/, "constant.numeric.hex.podlog"], // Hex
      [/-?\\d+/, "constant.numeric.integer.podlog"], // Integer

      // String Literals
      [
        /"/,
        {
          token: "string.quoted.double.podlog",
          bracket: "@open",
          next: "@string_double",
        },
      ],
      [
        /'/,
        {
          token: "string.quoted.single.podlog",
          bracket: "@open",
          next: "@string_single",
        },
      ],

      // Variables: start with '?', use explicit char class
      [/\\?[a-zA-Z_][a-zA-Z0-9_]*/, "variable.name.podlog"], // More specific token

      // Identifiers and keywords: general case
      [
        /[a-zA-Z_][a-zA-Z0-9_]*/,
        {
          cases: {
            "@keywords": "keyword.control.podlog", // More specific token
            "@default": "identifier.podlog",
          },
        },
      ],

      // Delimiters and brackets
      [/[\\[\\]]/, "delimiter.square.podlog"], // For arrays/sets
      [/[\\{\\}]/, "delimiter.curly.podlog"], // For dictionaries
      [/[()]/, "delimiter.parenthesis.podlog"],
      [/,/, "delimiter.comma.podlog"],
      [/:/, "delimiter.colon.podlog"],

      // Other symbols treated as operators if not covered above
      [/[=><!~?&|+*\/%#^\\-]+/, "operator.podlog"],
    ],

    comment: [
      [/[^\\/*]+/, "comment.block.podlog"], // More specific
      [/\/\*/, "comment.block.podlog", "@push"],
      ["\\\\*\/", "comment.block.podlog", "@pop"],
      [/[\/*]/, "comment.block.podlog"],
    ],

    string_double: [
      // Renamed from 'string'
      [/[^\\\\"]+/, "string.quoted.double.podlog"],
      [/@escapes/, "string.escape.char.podlog"],
      [/\\\\./, "string.escape.invalid.podlog"],
      [
        /"/,
        {
          token: "string.quoted.double.podlog",
          bracket: "@close",
          next: "@pop",
        },
      ],
    ],

    string_single: [
      // Added for single-quoted strings
      [/[^\\\\']+/, "string.quoted.single.podlog"],
      [/@escapes/, "string.escape.char.podlog"],
      [/\\\\./, "string.escape.invalid.podlog"],
      [
        /'/,
        {
          token: "string.quoted.single.podlog",
          bracket: "@close",
          next: "@pop",
        },
      ],
    ],

    whitespace: [
      [/[ \\t\\r\\n]+/, "white"], // Kept as 'white' or could be 'whitespace.podlog'
      [/\/\//, "comment.line.podlog", "@commentLine"], // More specific
    ],

    commentLine: [
      [/.*/, "comment.line.podlog", "@pop"], // More specific
    ],
  },
} as languages.IMonarchLanguage;
