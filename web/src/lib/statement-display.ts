import { z } from "zod";
import { ValueType as PodValueType } from "./types";

// Core value types
interface ValueType {
  String?: string;
  Int?: string;
  Bool?: boolean;
  Raw?: string;
  Array?: ValueType[];
  Set?: ValueType[];
  Dictionary?: Record<string, ValueType>;
}

const ValueSchema: z.ZodType<ValueType> = z.union([
  z.object({
    String: z.string()
  }),
  z.object({
    Int: z.string()
  }),
  z.object({
    Bool: z.boolean()
  }),
  z.object({
    Raw: z.string().regex(/^[0-9a-fA-F]{64}$/)
  }),
  z.object({
    Array: z.lazy(() => z.array(ValueSchema))
  }),
  z.object({
    Set: z.lazy(() => z.array(ValueSchema))
  }),
  z.object({
    Dictionary: z.lazy(() => z.record(z.string(), ValueSchema))
  })
]);

const OriginSchema = z.object({
  pod_class: z.enum(["Signed", "Main"]),
  pod_id: z.string().regex(/^[0-9a-fA-F]{64}$/)
});

const AnchoredKeySchema = z.object({
  origin: OriginSchema,
  key: z.string()
});

const StatementArgSchema = z.union([
  z.object({
    Key: AnchoredKeySchema
  }),
  z.object({
    Literal: ValueSchema
  })
]);

const PredicateSchema = z.discriminatedUnion("type", [
  z.object({
    type: z.literal("Native"),
    value: z.enum([
      "None",
      "ValueOf",
      "Equal",
      "NotEqual",
      "Gt",
      "Lt",
      "Contains",
      "NotContains",
      "SumOf",
      "ProductOf",
      "MaxOf"
    ])
  }),
  z.object({
    type: z.literal("BatchSelf"),
    value: z.number().int().nonnegative()
  }),
  z.object({
    type: z.literal("Custom"),
    value: z.tuple([
      z.object({
        name: z.string(),
        predicates: z.array(
          z.object({
            conjunction: z.boolean(),
            statements: z.array(
              z.tuple([
                z.any(), // Predicate
                z.array(z.any()) // StatementTmplArg array
              ])
            ),
            args_len: z.number().int().nonnegative()
          })
        )
      }),
      z.number().int().nonnegative()
    ])
  })
]);

const StatementSchema = z.object({
  predicate: PredicateSchema,
  args: z.array(StatementArgSchema)
});

// Types derived from schemas
export type Value = z.infer<typeof ValueSchema>;
export type Origin = z.infer<typeof OriginSchema>;
export type AnchoredKey = z.infer<typeof AnchoredKeySchema>;
export type StatementArg = z.infer<typeof StatementArgSchema>;
export type Predicate = z.infer<typeof PredicateSchema>;
export type Statement = z.infer<typeof StatementSchema>;

function shortenId(id: string): string {
  return id.slice(0, 6);
}

// Display functions
export function formatValue(value: ValueType): string {
  const type = Object.keys(value)[0] as keyof ValueType;
  const val = value[type];

  switch (type) {
    case "Raw":
      return `Raw:${shortenId(val as string)}`;
    case PodValueType.Array:
      return "Array";
    case PodValueType.Set:
      return "Set";
    case PodValueType.Dictionary:
      return "Dictionary";
    default:
      return `${type}:${val}`;
  }
}

export function formatAnchoredKey(key: AnchoredKey): string {
  return `${key.origin.pod_class}:${shortenId(key.origin.pod_id)}.${key.key}`;
}

export function formatArg(arg: StatementArg): string {
  if ("Key" in arg) {
    const { origin, key } = arg.Key;
    return `${origin.pod_class}:${shortenId(origin.pod_id)}.${key}`;
  } else if ("Literal" in arg) {
    return formatValue(arg.Literal);
  }
  return "";
}

export function formatStatement(statement: Statement): string {
  const { predicate, args } = statement;
  if (predicate.type !== "Native") return "";

  // Special handling for ValueOf which typically has one argument
  if (predicate.value === "ValueOf" && args.length > 0) {
    return `${predicate.value}(${formatArg(args[0])})`;
  }

  // For other predicates that typically have two arguments
  const formattedArgs = args.map(formatArg).filter((arg) => arg !== "");
  return `${predicate.value}(${formattedArgs.join(", ")})`;
}

// Validation functions
export const validateStatement = (data: unknown): Statement => {
  return StatementSchema.parse(data);
};

export const validateStatements = (data: unknown): Statement[] => {
  return z.array(StatementSchema).parse(data);
};
