import { createFileRoute } from "@tanstack/react-router";
import { LoginForm } from "../components/LoginForm";
import { useUser } from "../contexts/UserContext";
import Chance from "chance";
import { serialize } from "@/lib/Pod2Values";
import { createErr, createOk, isOk, type Result } from "option-t/plain_result";
import type { SignedPod } from "@/types/pod2";
import { useState, useTransition } from "react";

export const Route = createFileRoute("/zoo-gov")({
  component: RouteComponent,
});

export type DeelUser = {
  email: string;
  firstName: string;
  lastName: string;
  startDate: bigint;
  annualSalary: bigint;
  socialSecurityNumber: string;
};

export async function getDeelUserByEmail(
  email: string
): Promise<DeelUser | null> {
  // randomly generate DeelUser fields

  const chance = new Chance();

  const names = email.replace(/@zoo.com$/, "").split(".");
  if (names.length < 2) {
    return null;
  }

  const startDate = chance.birthday({
    year: chance.year({ min: 2000, max: 2022 }),
  }) as Date;
  const annualSalary = chance.integer({ min: 20000, max: 1000000 });
  const ssn = chance.ssn();

  const deelUser = {
    email,
    firstName: names[0].charAt(0).toUpperCase() + names[0].slice(1),
    lastName: names[1].charAt(0).toUpperCase() + names[1].slice(1),
    startDate: BigInt(startDate.getTime()),
    annualSalary: BigInt(annualSalary),
    socialSecurityNumber: ssn,
  };

  return deelUser;
}

async function issuePaystubPod(
  email: string,
  password: string
): Promise<Result<SignedPod, Error>> {
  const user = await getDeelUserByEmail(email);
  if (!user) {
    return createErr(new Error("User not found"));
  }

  const request = {
    private_key: password,
    entries: Object.fromEntries(
      Object.entries(user).map(([key, value]) => [key, serialize(value)])
    ),
  };
  console.log(request);

  try {
    const pod = await fetch(`${import.meta.env.VITE_API_URL}/api/pods/sign`, {
      method: "POST",
      body: JSON.stringify(request),
      headers: {
        "Content-Type": "application/json",
      },
    });
    const data: SignedPod = await pod.json();
    return createOk(data);
  } catch (e) {
    return createErr(e as Error);
  }
}

function SignPodComponent({
  publicKey,
  email,
  password,
  onLogout,
}: {
  publicKey: string;
  email: string;
  password: string;
  onLogout: () => void;
}) {
  const [result, setResult] = useState<Result<SignedPod, Error> | null>(null);
  const [isPending, startTransition] = useTransition();
  const [isCopied, setIsCopied] = useState(false);
  return (
    <>
      <title>ZooDeel</title>
      <div className="container mx-auto my-4">
        <div className="flex justify-between items-center mb-4">
          <h1 className="text-2xl font-bold mb-4">ZooDeel</h1>
          <button
            onClick={onLogout}
            className="bg-red-500 hover:bg-red-600 text-white font-medium py-2 px-4 rounded"
          >
            Logout
          </button>
        </div>
        <h2 className="text-xl font-bold mb-4">Paystub POD Issuer</h2>
        <p className="mb-4">
          Public Key:{" "}
          <code className="bg-gray-100 p-1 rounded">{publicKey}</code>
        </p>
        <button
          className="bg-blue-500 hover:bg-blue-600 text-white font-medium py-2 px-4 rounded"
          disabled={isPending}
          onClick={() => {
            startTransition(() => {
              return issuePaystubPod(email, password).then(setResult);
            });
          }}
        >
          Issue new Paystub POD
        </button>
        {result && isOk(result) && (
          <div className="mt-4 flex flex-col gap-4">
            <h2 className="text-lg font-bold">Here is your Paystub POD</h2>
            <div>
              <button
                className="bg-gray-200 hover:bg-gray-300 text-gray-800 font-medium py-2 px-4 rounded"
                onClick={() => {
                  navigator.clipboard.writeText(
                    JSON.stringify(result.val, null, 2)
                  );
                  setIsCopied(true);
                  setTimeout(() => {
                    setIsCopied(false);
                  }, 2000);
                }}
              >
                {isCopied ? "✅ Copied" : "📋 Copy to clipboard"}
              </button>
            </div>
            <textarea
              className="w-full bg-gray-100 p-2 rounded font-mono resize-none"
              rows={23}
              readOnly
              value={JSON.stringify(result.val, null, 2)}
            />
          </div>
        )}
      </div>
    </>
  );
}

function RouteComponent() {
  const { publicKey, username, password, isLoggedIn, login, logout } =
    useUser();

  return isLoggedIn ? (
    <SignPodComponent
      publicKey={publicKey}
      email={username}
      password={password}
      onLogout={logout}
    />
  ) : (
    <LoginForm onLogin={login} title="Login to Zoo Gov" />
  );
}
