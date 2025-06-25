import Chance from "chance";
import { useState, useTransition } from "react";

interface LoginFormProps {
  onLogin: (username: string, password: string) => Promise<void>;
  title: string;
}

function generateUsername() {
  const chance = new Chance();
  const animal = chance.animal().replace(/'| /g, "");
  const names = animal.split(" ");
  if (names.length < 2) {
    names.push(chance.last().replace(/'| /g, ""));
  }
  const name = names.join(".").toLowerCase();
  return `${name}@zoo.com`;
}

function generatePassword() {
  const chance = new Chance();
  return `zoo${chance.string({ length: 6 })}`;
}

export function LoginForm({ onLogin, title }: LoginFormProps) {
  const [username, setUsername] = useState(generateUsername());
  const [password, setPassword] = useState(generatePassword());
  const [isPending, startTransition] = useTransition();

  const handleSubmit = (e: React.FormEvent) => {
    e.preventDefault();
    if (username && password) {
      startTransition(async () => {
        await onLogin(username, password);
      });
    }
  };

  return (
    <>
      <title>{title}</title>
      <div className="max-w-md mx-auto mt-10 p-6 bg-white rounded-lg shadow-md">
        <h1 className="text-2xl font-bold mb-6 text-center">{title}</h1>
        <form onSubmit={handleSubmit} className="space-y-4">
          <div>
            <label
              htmlFor="username"
              className="block text-sm font-medium text-gray-700 mb-1"
            >
              Username:
            </label>
            <input
              type="text"
              id="username"
              value={username}
              onChange={(e) => setUsername(e.target.value)}
              required
              disabled={isPending}
              className="w-full px-3 py-2 border border-gray-300 rounded-md focus:outline-none focus:ring-2 focus:ring-blue-500 disabled:bg-gray-100 disabled:text-gray-500"
            />
          </div>
          <div>
            <label
              htmlFor="password"
              className="block text-sm font-medium text-gray-700 mb-1"
            >
              Password:
            </label>
            <input
              type="password"
              id="password"
              value={password}
              onChange={(e) => setPassword(e.target.value)}
              required
              disabled={isPending}
              className="w-full px-3 py-2 border border-gray-300 rounded-md focus:outline-none focus:ring-2 focus:ring-blue-500 disabled:bg-gray-100 disabled:text-gray-500"
            />
          </div>
          <button
            type="submit"
            disabled={isPending}
            className="w-full bg-blue-500 hover:bg-blue-600 text-white font-medium py-2 px-4 rounded disabled:bg-blue-300 disabled:cursor-not-allowed"
          >
            {isPending ? "Logging in..." : "Login"}
          </button>
        </form>
      </div>
    </>
  );
}
